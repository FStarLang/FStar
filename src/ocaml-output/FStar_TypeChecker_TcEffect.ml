
open Prims
open FStar_Pervasives

let dmff_cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option) = (fun env ed -> (FStar_TypeChecker_DMFF.cps_and_elaborate env ed))


let tc_layered_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed quals -> ((

let uu____41 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____41) with
| true -> begin
(

let uu____46 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____46))
end
| uu____50 -> begin
()
end));
(match (((Prims.op_disEquality (FStar_List.length ed.FStar_Syntax_Syntax.univs) (Prims.parse_int "0")) || (Prims.op_disEquality (FStar_List.length ed.FStar_Syntax_Syntax.binders) (Prims.parse_int "0")))) with
| true -> begin
(

let uu____64 = (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.op_Hat "Binders are not supported for layered effects (" (Prims.op_Hat ed.FStar_Syntax_Syntax.mname.FStar_Ident.str ")")))) uu____64))
end
| uu____68 -> begin
()
end);
(

let check_and_gen = (fun comb n1 uu____97 -> (match (uu____97) with
| (us, t) -> begin
(

let uu____118 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____118) with
| (us1, t1) -> begin
(

let uu____131 = (

let uu____136 = (

let uu____143 = (FStar_TypeChecker_Env.push_univ_vars env0 us1)
in (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____143 t1))
in (match (uu____136) with
| (t2, lc, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env0 g);
((t2), (lc.FStar_TypeChecker_Common.res_typ));
)
end))
in (match (uu____131) with
| (t2, ty) -> begin
(

let uu____160 = (FStar_TypeChecker_Util.generalize_universes env0 t2)
in (match (uu____160) with
| (g_us, t3) -> begin
(

let ty1 = (FStar_Syntax_Subst.close_univ_vars g_us ty)
in ((match ((Prims.op_disEquality (FStar_List.length g_us) n1)) with
| true -> begin
(

let error = (

let uu____183 = (FStar_Util.string_of_int n1)
in (

let uu____185 = (

let uu____187 = (FStar_All.pipe_right g_us FStar_List.length)
in (FStar_All.pipe_right uu____187 FStar_Util.string_of_int))
in (

let uu____194 = (FStar_Syntax_Print.tscheme_to_string ((g_us), (t3)))
in (FStar_Util.format5 "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str comb uu____183 uu____185 uu____194))))
in ((FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (error)) t3.FStar_Syntax_Syntax.pos);
(match (us1) with
| [] -> begin
()
end
| uu____203 -> begin
(

let uu____204 = ((Prims.op_Equality (FStar_List.length us1) (FStar_List.length g_us)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____211 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____211 (Prims.parse_int "0")))) us1 g_us))
in (match (uu____204) with
| true -> begin
()
end
| uu____216 -> begin
(

let uu____218 = (

let uu____224 = (

let uu____226 = (FStar_Syntax_Print.univ_names_to_string us1)
in (

let uu____228 = (FStar_Syntax_Print.univ_names_to_string g_us)
in (FStar_Util.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str comb uu____226 uu____228)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____224)))
in (FStar_Errors.raise_error uu____218 t3.FStar_Syntax_Syntax.pos))
end))
end);
))
end
| uu____232 -> begin
()
end);
((g_us), (t3), (ty1));
))
end))
end))
end))
end))
in (

let log_combinator = (fun s uu____257 -> (match (uu____257) with
| (us, t, ty) -> begin
(

let uu____286 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____286) with
| true -> begin
(

let uu____291 = (FStar_Syntax_Print.tscheme_to_string ((us), (t)))
in (

let uu____297 = (FStar_Syntax_Print.tscheme_to_string ((us), (ty)))
in (FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str s uu____291 uu____297)))
end
| uu____304 -> begin
()
end))
end))
in (

let fresh_a_and_u_a = (fun a -> (

let uu____322 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____322 (fun uu____339 -> (match (uu____339) with
| (t, u) -> begin
(

let uu____350 = (

let uu____351 = (FStar_Syntax_Syntax.gen_bv a FStar_Pervasives_Native.None t)
in (FStar_All.pipe_right uu____351 FStar_Syntax_Syntax.mk_binder))
in ((uu____350), (u)))
end)))))
in (

let fresh_x_a = (fun x a -> (

let uu____365 = (

let uu____366 = (

let uu____367 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____367 FStar_Syntax_Syntax.bv_to_name))
in (FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None uu____366))
in (FStar_All.pipe_right uu____365 FStar_Syntax_Syntax.mk_binder)))
in (

let signature = (

let r = (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
in (

let uu____394 = (check_and_gen "signature" (Prims.parse_int "1") ed.FStar_Syntax_Syntax.signature)
in (match (uu____394) with
| (sig_us, sig_t, sig_ty) -> begin
(

let uu____418 = (FStar_Syntax_Subst.open_univ_vars sig_us sig_t)
in (match (uu____418) with
| (us, t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____438 = (fresh_a_and_u_a "a")
in (match (uu____438) with
| (a, u) -> begin
(

let rest_bs = (

let uu____459 = (

let uu____460 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____460 FStar_Syntax_Syntax.bv_to_name))
in (FStar_TypeChecker_Util.layered_effect_indices_as_binders env r ed.FStar_Syntax_Syntax.mname ((sig_us), (sig_t)) u uu____459))
in (

let bs = (a)::rest_bs
in (

let k = (

let uu____491 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow bs uu____491))
in (

let g_eq = (FStar_TypeChecker_Rel.teq env t k)
in ((FStar_TypeChecker_Rel.force_trivial_guard env g_eq);
(

let uu____496 = (

let uu____499 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_Syntax_Subst.close_univ_vars us uu____499))
in ((sig_us), (uu____496), (sig_ty)));
)))))
end)))
end))
end)))
in ((log_combinator "signature" signature);
(

let uu____508 = (

let repr_ts = (

let uu____530 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr)
in (FStar_All.pipe_right uu____530 FStar_Util.must))
in (

let r = (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
in (

let uu____558 = (check_and_gen "repr" (Prims.parse_int "1") repr_ts)
in (match (uu____558) with
| (repr_us, repr_t, repr_ty) -> begin
(

let underlying_effect_lid = (

let repr_t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "0"))))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env0 repr_t)
in (

let uu____589 = (

let uu____590 = (FStar_Syntax_Subst.compress repr_t1)
in uu____590.FStar_Syntax_Syntax.n)
in (match (uu____589) with
| FStar_Syntax_Syntax.Tm_abs (uu____593, t, uu____595) -> begin
(

let uu____620 = (

let uu____621 = (FStar_Syntax_Subst.compress t)
in uu____621.FStar_Syntax_Syntax.n)
in (match (uu____620) with
| FStar_Syntax_Syntax.Tm_arrow (uu____624, c) -> begin
(

let uu____646 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name)
in (FStar_All.pipe_right uu____646 (FStar_TypeChecker_Env.norm_eff_name env0)))
end
| uu____649 -> begin
(

let uu____650 = (

let uu____656 = (

let uu____658 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname FStar_Ident.string_of_lid)
in (

let uu____661 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "repr body for %s is not an arrow (%s)" uu____658 uu____661)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____656)))
in (FStar_Errors.raise_error uu____650 r))
end))
end
| uu____665 -> begin
(

let uu____666 = (

let uu____672 = (

let uu____674 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname FStar_Ident.string_of_lid)
in (

let uu____677 = (FStar_Syntax_Print.term_to_string repr_t1)
in (FStar_Util.format2 "repr for %s is not an abstraction (%s)" uu____674 uu____677)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____672)))
in (FStar_Errors.raise_error uu____666 r))
end)))
in ((

let uu____682 = ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)) && (

let uu____688 = (FStar_TypeChecker_Env.is_total_effect env0 underlying_effect_lid)
in (not (uu____688))))
in (match (uu____682) with
| true -> begin
(

let uu____691 = (

let uu____697 = (

let uu____699 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname FStar_Ident.string_of_lid)
in (

let uu____702 = (FStar_All.pipe_right underlying_effect_lid FStar_Ident.string_of_lid)
in (FStar_Util.format2 "Effect %s is marked total but its underlying effect %s is not total" uu____699 uu____702)))
in ((FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal), (uu____697)))
in (FStar_Errors.raise_error uu____691 r))
end
| uu____707 -> begin
()
end));
(

let uu____709 = (FStar_Syntax_Subst.open_univ_vars repr_us repr_ty)
in (match (uu____709) with
| (us, ty) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____733 = (fresh_a_and_u_a "a")
in (match (uu____733) with
| (a, u) -> begin
(

let rest_bs = (

let signature_ts = (

let uu____759 = signature
in (match (uu____759) with
| (us1, t, uu____774) -> begin
((us1), (t))
end))
in (

let uu____791 = (

let uu____792 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____792 FStar_Syntax_Syntax.bv_to_name))
in (FStar_TypeChecker_Util.layered_effect_indices_as_binders env r ed.FStar_Syntax_Syntax.mname signature_ts u uu____791)))
in (

let bs = (a)::rest_bs
in (

let k = (

let uu____819 = (

let uu____822 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____822 (fun uu____835 -> (match (uu____835) with
| (t, u1) -> begin
(

let uu____842 = (

let uu____845 = (FStar_TypeChecker_Env.new_u_univ ())
in FStar_Pervasives_Native.Some (uu____845))
in (FStar_Syntax_Syntax.mk_Total' t uu____842))
end))))
in (FStar_Syntax_Util.arrow bs uu____819))
in (

let g = (FStar_TypeChecker_Rel.teq env ty k)
in ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let uu____848 = (

let uu____861 = (

let uu____864 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_Syntax_Subst.close_univ_vars us uu____864))
in ((repr_us), (repr_t), (uu____861)))
in ((uu____848), (underlying_effect_lid)));
)))))
end)))
end));
))
end))))
in (match (uu____508) with
| (repr, underlying_effect_lid) -> begin
((log_combinator "repr" repr);
(

let fresh_repr = (fun r env u a_tm -> (

let signature_ts = (

let uu____937 = signature
in (match (uu____937) with
| (us, t, uu____952) -> begin
((us), (t))
end))
in (

let repr_ts = (

let uu____970 = repr
in (match (uu____970) with
| (us, t, uu____985) -> begin
((us), (t))
end))
in (FStar_TypeChecker_Util.fresh_effect_repr env r ed.FStar_Syntax_Syntax.mname signature_ts (FStar_Pervasives_Native.Some (repr_ts)) u a_tm))))
in (

let not_an_arrow_error = (fun comb n1 t r -> (

let uu____1035 = (

let uu____1041 = (

let uu____1043 = (FStar_Util.string_of_int n1)
in (

let uu____1045 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____1047 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format5 "Type of %s:%s is not an arrow with >= %s binders (%s::%s)" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str comb uu____1043 uu____1045 uu____1047))))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____1041)))
in (FStar_Errors.raise_error uu____1035 r)))
in (

let return_repr = (

let return_repr_ts = (

let uu____1077 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr)
in (FStar_All.pipe_right uu____1077 FStar_Util.must))
in (

let r = (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
in (

let uu____1105 = (check_and_gen "return_repr" (Prims.parse_int "1") return_repr_ts)
in (match (uu____1105) with
| (ret_us, ret_t, ret_ty) -> begin
(

let uu____1129 = (FStar_Syntax_Subst.open_univ_vars ret_us ret_ty)
in (match (uu____1129) with
| (us, ty) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____1149 = (fresh_a_and_u_a "a")
in (match (uu____1149) with
| (a, u_a) -> begin
(

let rest_bs = (

let uu____1178 = (

let uu____1179 = (FStar_Syntax_Subst.compress ty)
in uu____1179.FStar_Syntax_Syntax.n)
in (match (uu____1178) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____1191) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____1219 = (FStar_Syntax_Subst.open_binders bs)
in (match (uu____1219) with
| ((a', uu____1229))::(uu____1230)::bs1 -> begin
(

let uu____1262 = (

let uu____1275 = (

let uu____1278 = (

let uu____1279 = (

let uu____1286 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst a))
in ((a'), (uu____1286)))
in FStar_Syntax_Syntax.NT (uu____1279))
in (uu____1278)::[])
in (FStar_Syntax_Subst.subst_binders uu____1275))
in (FStar_All.pipe_right bs1 uu____1262))
end))
end
| uu____1301 -> begin
(not_an_arrow_error "return" (Prims.parse_int "2") ty r)
end))
in (

let bs = (

let uu____1313 = (

let uu____1322 = (fresh_x_a "x" a)
in (uu____1322)::rest_bs)
in (a)::uu____1313)
in (

let uu____1342 = (

let uu____1347 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____1348 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____1347 u_a uu____1348)))
in (match (uu____1342) with
| (repr1, g) -> begin
(

let k = (

let uu____1368 = (FStar_Syntax_Syntax.mk_Total' repr1 (FStar_Pervasives_Native.Some (u_a)))
in (FStar_Syntax_Util.arrow bs uu____1368))
in (

let g_eq = (FStar_TypeChecker_Rel.teq env ty k)
in ((

let uu____1373 = (FStar_TypeChecker_Env.conj_guard g g_eq)
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____1373));
(

let uu____1374 = (

let uu____1377 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_Syntax_Subst.close_univ_vars us uu____1377))
in ((ret_us), (ret_t), (uu____1374)));
)))
end))))
end)))
end))
end))))
in ((log_combinator "return_repr" return_repr);
(

let bind_repr = (

let bind_repr_ts = (

let uu____1404 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr)
in (FStar_All.pipe_right uu____1404 FStar_Util.must))
in (

let r = (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
in (

let uu____1416 = (check_and_gen "bind_repr" (Prims.parse_int "2") bind_repr_ts)
in (match (uu____1416) with
| (bind_us, bind_t, bind_ty) -> begin
(

let uu____1440 = (FStar_Syntax_Subst.open_univ_vars bind_us bind_ty)
in (match (uu____1440) with
| (us, ty) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____1460 = (fresh_a_and_u_a "a")
in (match (uu____1460) with
| (a, u_a) -> begin
(

let uu____1480 = (fresh_a_and_u_a "b")
in (match (uu____1480) with
| (b, u_b) -> begin
(

let rest_bs = (

let uu____1509 = (

let uu____1510 = (FStar_Syntax_Subst.compress ty)
in uu____1510.FStar_Syntax_Syntax.n)
in (match (uu____1509) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____1522) when ((FStar_List.length bs) >= (Prims.parse_int "4")) -> begin
(

let uu____1550 = (FStar_Syntax_Subst.open_binders bs)
in (match (uu____1550) with
| ((a', uu____1560))::((b', uu____1562))::bs1 -> begin
(

let uu____1592 = (

let uu____1593 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "2"))))
in (FStar_All.pipe_right uu____1593 FStar_Pervasives_Native.fst))
in (

let uu____1691 = (

let uu____1704 = (

let uu____1707 = (

let uu____1708 = (

let uu____1715 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst a))
in ((a'), (uu____1715)))
in FStar_Syntax_Syntax.NT (uu____1708))
in (

let uu____1722 = (

let uu____1725 = (

let uu____1726 = (

let uu____1733 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in ((b'), (uu____1733)))
in FStar_Syntax_Syntax.NT (uu____1726))
in (uu____1725)::[])
in (uu____1707)::uu____1722))
in (FStar_Syntax_Subst.subst_binders uu____1704))
in (FStar_All.pipe_right uu____1592 uu____1691)))
end))
end
| uu____1748 -> begin
(not_an_arrow_error "bind" (Prims.parse_int "4") ty r)
end))
in (

let bs = (a)::(b)::rest_bs
in (

let uu____1772 = (

let uu____1783 = (

let uu____1788 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____1789 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____1788 u_a uu____1789)))
in (match (uu____1783) with
| (repr1, g) -> begin
(

let uu____1804 = (

let uu____1811 = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None repr1)
in (FStar_All.pipe_right uu____1811 FStar_Syntax_Syntax.mk_binder))
in ((uu____1804), (g)))
end))
in (match (uu____1772) with
| (f, guard_f) -> begin
(

let uu____1851 = (

let x_a = (fresh_x_a "x" a)
in (

let uu____1864 = (

let uu____1869 = (FStar_TypeChecker_Env.push_binders env (FStar_List.append bs ((x_a)::[])))
in (

let uu____1888 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst b) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____1869 u_b uu____1888)))
in (match (uu____1864) with
| (repr1, g) -> begin
(

let uu____1903 = (

let uu____1910 = (

let uu____1911 = (

let uu____1912 = (

let uu____1915 = (

let uu____1918 = (FStar_TypeChecker_Env.new_u_univ ())
in FStar_Pervasives_Native.Some (uu____1918))
in (FStar_Syntax_Syntax.mk_Total' repr1 uu____1915))
in (FStar_Syntax_Util.arrow ((x_a)::[]) uu____1912))
in (FStar_Syntax_Syntax.gen_bv "g" FStar_Pervasives_Native.None uu____1911))
in (FStar_All.pipe_right uu____1910 FStar_Syntax_Syntax.mk_binder))
in ((uu____1903), (g)))
end)))
in (match (uu____1851) with
| (g, guard_g) -> begin
(

let uu____1970 = (

let uu____1975 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____1976 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst b) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____1975 u_b uu____1976)))
in (match (uu____1970) with
| (repr1, guard_repr) -> begin
(

let k = (

let uu____1996 = (FStar_Syntax_Syntax.mk_Total' repr1 (FStar_Pervasives_Native.Some (u_b)))
in (FStar_Syntax_Util.arrow (FStar_List.append bs ((f)::(g)::[])) uu____1996))
in (

let guard_eq = (FStar_TypeChecker_Rel.teq env ty k)
in ((FStar_List.iter (FStar_TypeChecker_Rel.force_trivial_guard env) ((guard_f)::(guard_g)::(guard_repr)::(guard_eq)::[]));
(

let uu____2025 = (

let uu____2028 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_Syntax_Subst.close_univ_vars bind_us uu____2028))
in ((bind_us), (bind_t), (uu____2025)));
)))
end))
end))
end))))
end))
end)))
end))
end))))
in ((log_combinator "bind_repr" bind_repr);
(

let stronger_repr = (

let stronger_repr = (

let uu____2055 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_stronger_repr)
in (FStar_All.pipe_right uu____2055 FStar_Util.must))
in (

let r = (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
in (

let uu____2083 = (check_and_gen "stronger_repr" (Prims.parse_int "1") stronger_repr)
in (match (uu____2083) with
| (stronger_us, stronger_t, stronger_ty) -> begin
((

let uu____2108 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____2108) with
| true -> begin
(

let uu____2113 = (FStar_Syntax_Print.tscheme_to_string ((stronger_us), (stronger_t)))
in (

let uu____2119 = (FStar_Syntax_Print.tscheme_to_string ((stronger_us), (stronger_ty)))
in (FStar_Util.print2 "stronger combinator typechecked with term: %s and type: %s\n" uu____2113 uu____2119)))
end
| uu____2126 -> begin
()
end));
(

let uu____2128 = (FStar_Syntax_Subst.open_univ_vars stronger_us stronger_ty)
in (match (uu____2128) with
| (us, ty) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____2148 = (fresh_a_and_u_a "a")
in (match (uu____2148) with
| (a, u) -> begin
(

let rest_bs = (

let uu____2177 = (

let uu____2178 = (FStar_Syntax_Subst.compress ty)
in uu____2178.FStar_Syntax_Syntax.n)
in (match (uu____2177) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____2190) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____2218 = (FStar_Syntax_Subst.open_binders bs)
in (match (uu____2218) with
| ((a', uu____2228))::bs1 -> begin
(

let uu____2248 = (

let uu____2249 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "1"))))
in (FStar_All.pipe_right uu____2249 FStar_Pervasives_Native.fst))
in (

let uu____2347 = (

let uu____2360 = (

let uu____2363 = (

let uu____2364 = (

let uu____2371 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst a))
in ((a'), (uu____2371)))
in FStar_Syntax_Syntax.NT (uu____2364))
in (uu____2363)::[])
in (FStar_Syntax_Subst.subst_binders uu____2360))
in (FStar_All.pipe_right uu____2248 uu____2347)))
end))
end
| uu____2386 -> begin
(not_an_arrow_error "stronger" (Prims.parse_int "2") ty r)
end))
in (

let bs = (a)::rest_bs
in (

let uu____2404 = (

let uu____2415 = (

let uu____2420 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____2421 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____2420 u uu____2421)))
in (match (uu____2415) with
| (repr1, g) -> begin
(

let uu____2436 = (

let uu____2443 = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None repr1)
in (FStar_All.pipe_right uu____2443 FStar_Syntax_Syntax.mk_binder))
in ((uu____2436), (g)))
end))
in (match (uu____2404) with
| (f, guard_f) -> begin
(

let uu____2483 = (

let uu____2488 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____2489 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) FStar_Syntax_Syntax.bv_to_name)
in (fresh_repr r uu____2488 u uu____2489)))
in (match (uu____2483) with
| (ret_t, guard_ret_t) -> begin
(

let pure_wp_t = (

let pure_wp_ts = (

let uu____2508 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.NoDelta)::[]) env FStar_Parser_Const.pure_wp_lid)
in (FStar_All.pipe_right uu____2508 FStar_Util.must))
in (

let uu____2525 = (FStar_TypeChecker_Env.inst_tscheme pure_wp_ts)
in (match (uu____2525) with
| (uu____2530, pure_wp_t) -> begin
(

let uu____2532 = (

let uu____2537 = (

let uu____2538 = (FStar_All.pipe_right ret_t FStar_Syntax_Syntax.as_arg)
in (uu____2538)::[])
in (FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____2537))
in (uu____2532 FStar_Pervasives_Native.None r))
end)))
in (

let uu____2571 = (

let reason = (FStar_Util.format1 "implicit for pure_wp in checking stronger for %s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str)
in (

let uu____2587 = (FStar_TypeChecker_Env.push_binders env bs)
in (FStar_TypeChecker_Util.new_implicit_var reason r uu____2587 pure_wp_t)))
in (match (uu____2571) with
| (pure_wp_uvar, uu____2601, guard_wp) -> begin
(

let c = (

let uu____2616 = (

let uu____2617 = (

let uu____2618 = (FStar_TypeChecker_Env.new_u_univ ())
in (uu____2618)::[])
in (

let uu____2619 = (

let uu____2630 = (FStar_All.pipe_right pure_wp_uvar FStar_Syntax_Syntax.as_arg)
in (uu____2630)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2617; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = ret_t; FStar_Syntax_Syntax.effect_args = uu____2619; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____2616))
in (

let k = (FStar_Syntax_Util.arrow (FStar_List.append bs ((f)::[])) c)
in ((

let uu____2685 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____2685) with
| true -> begin
(

let uu____2690 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print1 "Expected type before unification: %s\n" uu____2690))
end
| uu____2693 -> begin
()
end));
(

let guard_eq = (FStar_TypeChecker_Rel.teq env ty k)
in ((FStar_List.iter (FStar_TypeChecker_Rel.force_trivial_guard env) ((guard_f)::(guard_ret_t)::(guard_wp)::(guard_eq)::[]));
(

let k1 = (FStar_TypeChecker_Normalize.remove_uvar_solutions env k)
in (

let uu____2698 = (

let uu____2701 = (FStar_All.pipe_right k1 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::[]) env))
in (FStar_All.pipe_right uu____2701 (FStar_Syntax_Subst.close_univ_vars stronger_us)))
in ((stronger_us), (stronger_t), (uu____2698))));
));
)))
end)))
end))
end))))
end)))
end));
)
end))))
in ((log_combinator "stronger_repr" stronger_repr);
(

let if_then_else1 = (

let if_then_else_ts = (

let uu____2730 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_layered_if_then_else_combinator)
in (FStar_All.pipe_right uu____2730 FStar_Util.must))
in (

let r = (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
in (

let uu____2758 = (check_and_gen "if_then_else" (Prims.parse_int "1") if_then_else_ts)
in (match (uu____2758) with
| (if_then_else_us, if_then_else_t, if_then_else_ty) -> begin
(

let uu____2782 = (FStar_Syntax_Subst.open_univ_vars if_then_else_us if_then_else_t)
in (match (uu____2782) with
| (us, t) -> begin
(

let uu____2801 = (FStar_Syntax_Subst.open_univ_vars if_then_else_us if_then_else_ty)
in (match (uu____2801) with
| (uu____2818, ty) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let uu____2821 = (fresh_a_and_u_a "a")
in (match (uu____2821) with
| (a, u_a) -> begin
(

let rest_bs = (

let uu____2850 = (

let uu____2851 = (FStar_Syntax_Subst.compress ty)
in uu____2851.FStar_Syntax_Syntax.n)
in (match (uu____2850) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____2863) when ((FStar_List.length bs) >= (Prims.parse_int "4")) -> begin
(

let uu____2891 = (FStar_Syntax_Subst.open_binders bs)
in (match (uu____2891) with
| ((a', uu____2901))::bs1 -> begin
(

let uu____2921 = (

let uu____2922 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "3"))))
in (FStar_All.pipe_right uu____2922 FStar_Pervasives_Native.fst))
in (

let uu____3020 = (

let uu____3033 = (

let uu____3036 = (

let uu____3037 = (

let uu____3044 = (

let uu____3047 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3047 FStar_Syntax_Syntax.bv_to_name))
in ((a'), (uu____3044)))
in FStar_Syntax_Syntax.NT (uu____3037))
in (uu____3036)::[])
in (FStar_Syntax_Subst.subst_binders uu____3033))
in (FStar_All.pipe_right uu____2921 uu____3020)))
end))
end
| uu____3068 -> begin
(not_an_arrow_error "if_then_else" (Prims.parse_int "4") ty r)
end))
in (

let bs = (a)::rest_bs
in (

let uu____3086 = (

let uu____3097 = (

let uu____3102 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____3103 = (

let uu____3104 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3104 FStar_Syntax_Syntax.bv_to_name))
in (fresh_repr r uu____3102 u_a uu____3103)))
in (match (uu____3097) with
| (repr1, g) -> begin
(

let uu____3125 = (

let uu____3132 = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None repr1)
in (FStar_All.pipe_right uu____3132 FStar_Syntax_Syntax.mk_binder))
in ((uu____3125), (g)))
end))
in (match (uu____3086) with
| (f_bs, guard_f) -> begin
(

let uu____3172 = (

let uu____3183 = (

let uu____3188 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____3189 = (

let uu____3190 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3190 FStar_Syntax_Syntax.bv_to_name))
in (fresh_repr r uu____3188 u_a uu____3189)))
in (match (uu____3183) with
| (repr1, g) -> begin
(

let uu____3211 = (

let uu____3218 = (FStar_Syntax_Syntax.gen_bv "g" FStar_Pervasives_Native.None repr1)
in (FStar_All.pipe_right uu____3218 FStar_Syntax_Syntax.mk_binder))
in ((uu____3211), (g)))
end))
in (match (uu____3172) with
| (g_bs, guard_g) -> begin
(

let p_b = (

let uu____3265 = (FStar_Syntax_Syntax.gen_bv "p" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3265 FStar_Syntax_Syntax.mk_binder))
in (

let uu____3273 = (

let uu____3278 = (FStar_TypeChecker_Env.push_binders env (FStar_List.append bs ((p_b)::[])))
in (

let uu____3297 = (

let uu____3298 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____3298 FStar_Syntax_Syntax.bv_to_name))
in (fresh_repr r uu____3278 u_a uu____3297)))
in (match (uu____3273) with
| (t_body, guard_body) -> begin
(

let k = (FStar_Syntax_Util.abs (FStar_List.append bs ((f_bs)::(g_bs)::(p_b)::[])) t_body FStar_Pervasives_Native.None)
in (

let guard_eq = (FStar_TypeChecker_Rel.teq env t k)
in ((FStar_All.pipe_right ((guard_f)::(guard_g)::(guard_body)::(guard_eq)::[]) (FStar_List.iter (FStar_TypeChecker_Rel.force_trivial_guard env)));
(

let uu____3358 = (

let uu____3361 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_Syntax_Subst.close_univ_vars if_then_else_us uu____3361))
in ((if_then_else_us), (uu____3358), (if_then_else_ty)));
)))
end)))
end))
end))))
end)))
end))
end))
end))))
in ((log_combinator "if_then_else" if_then_else1);
(

let r = (

let uu____3372 = (

let uu____3375 = (

let uu____3384 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_layered_if_then_else_combinator)
in (FStar_All.pipe_right uu____3384 FStar_Util.must))
in (FStar_All.pipe_right uu____3375 FStar_Pervasives_Native.snd))
in uu____3372.FStar_Syntax_Syntax.pos)
in (

let uu____3413 = if_then_else1
in (match (uu____3413) with
| (ite_us, ite_t, uu____3428) -> begin
(

let uu____3441 = (FStar_Syntax_Subst.open_univ_vars ite_us ite_t)
in (match (uu____3441) with
| (us, ite_t1) -> begin
(

let uu____3448 = (

let uu____3459 = (

let uu____3460 = (FStar_Syntax_Subst.compress ite_t1)
in uu____3460.FStar_Syntax_Syntax.n)
in (match (uu____3459) with
| FStar_Syntax_Syntax.Tm_abs (bs, uu____3474, uu____3475) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (

let uu____3501 = (

let uu____3508 = (

let uu____3511 = (

let uu____3514 = (

let uu____3523 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "3"))))
in (FStar_All.pipe_right uu____3523 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____3514 (FStar_List.map FStar_Pervasives_Native.fst)))
in (FStar_All.pipe_right uu____3511 (FStar_List.map FStar_Syntax_Syntax.bv_to_name)))
in (FStar_All.pipe_right uu____3508 (fun l -> (

let uu____3667 = l
in (match (uu____3667) with
| (f)::(g)::(p)::[] -> begin
((f), (g), (p))
end)))))
in (match (uu____3501) with
| (f, g, p) -> begin
(

let uu____3692 = (

let uu____3693 = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (FStar_TypeChecker_Env.push_binders uu____3693 bs1))
in (

let uu____3694 = (

let uu____3695 = (

let uu____3700 = (

let uu____3701 = (

let uu____3704 = (FStar_All.pipe_right bs1 (FStar_List.map FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____3704 (FStar_List.map FStar_Syntax_Syntax.bv_to_name)))
in (FStar_All.pipe_right uu____3701 (FStar_List.map FStar_Syntax_Syntax.as_arg)))
in (FStar_Syntax_Syntax.mk_Tm_app ite_t1 uu____3700))
in (uu____3695 FStar_Pervasives_Native.None r))
in ((uu____3692), (uu____3694), (f), (g), (p))))
end)))
end
| uu____3731 -> begin
(failwith "Impossible! ite_t must have been an abstraction with at least 3 binders")
end))
in (match (uu____3448) with
| (env, ite_t_applied, f_t, g_t, p_t) -> begin
(

let uu____3748 = (

let uu____3757 = stronger_repr
in (match (uu____3757) with
| (uu____3778, subcomp_t, subcomp_ty) -> begin
(

let uu____3793 = (FStar_Syntax_Subst.open_univ_vars us subcomp_t)
in (match (uu____3793) with
| (uu____3806, subcomp_t1) -> begin
(

let bs_except_last = (

let uu____3817 = (FStar_Syntax_Subst.open_univ_vars us subcomp_ty)
in (match (uu____3817) with
| (uu____3830, subcomp_ty1) -> begin
(

let uu____3832 = (

let uu____3833 = (FStar_Syntax_Subst.compress subcomp_ty1)
in uu____3833.FStar_Syntax_Syntax.n)
in (match (uu____3832) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____3845) -> begin
(

let uu____3866 = (FStar_All.pipe_right bs (FStar_List.splitAt ((FStar_List.length bs) - (Prims.parse_int "1"))))
in (FStar_All.pipe_right uu____3866 FStar_Pervasives_Native.fst))
end
| uu____3972 -> begin
(failwith "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
end))
end))
in (

let aux = (fun t -> (

let uu____3990 = (

let uu____3995 = (

let uu____3996 = (

let uu____3999 = (FStar_All.pipe_right bs_except_last (FStar_List.map (fun uu____4019 -> FStar_Syntax_Syntax.tun)))
in (FStar_List.append uu____3999 ((t)::[])))
in (FStar_All.pipe_right uu____3996 (FStar_List.map FStar_Syntax_Syntax.as_arg)))
in (FStar_Syntax_Syntax.mk_Tm_app subcomp_t1 uu____3995))
in (uu____3990 FStar_Pervasives_Native.None r)))
in (

let uu____4028 = (aux f_t)
in (

let uu____4031 = (aux g_t)
in ((uu____4028), (uu____4031))))))
end))
end))
in (match (uu____3748) with
| (subcomp_f, subcomp_g) -> begin
(

let uu____4048 = (

let aux = (fun t -> (

let uu____4065 = (

let uu____4072 = (

let uu____4073 = (

let uu____4100 = (

let uu____4117 = (

let uu____4126 = (FStar_Syntax_Syntax.mk_Total ite_t_applied)
in FStar_Util.Inr (uu____4126))
in ((uu____4117), (FStar_Pervasives_Native.None)))
in ((t), (uu____4100), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4073))
in (FStar_Syntax_Syntax.mk uu____4072))
in (uu____4065 FStar_Pervasives_Native.None r)))
in (

let uu____4167 = (aux subcomp_f)
in (

let uu____4168 = (aux subcomp_g)
in ((uu____4167), (uu____4168)))))
in (match (uu____4048) with
| (tm_subcomp_ascribed_f, tm_subcomp_ascribed_g) -> begin
((

let uu____4172 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____4172) with
| true -> begin
(

let uu____4177 = (FStar_Syntax_Print.term_to_string tm_subcomp_ascribed_f)
in (

let uu____4179 = (FStar_Syntax_Print.term_to_string tm_subcomp_ascribed_g)
in (FStar_Util.print2 "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n" uu____4177 uu____4179)))
end
| uu____4182 -> begin
()
end));
(

let uu____4184 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env tm_subcomp_ascribed_f)
in (match (uu____4184) with
| (uu____4191, uu____4192, g_f) -> begin
(

let g_f1 = (

let uu____4195 = (FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (p_t)))
in (FStar_TypeChecker_Env.imp_guard uu____4195 g_f))
in ((FStar_TypeChecker_Rel.force_trivial_guard env g_f1);
(

let uu____4197 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env tm_subcomp_ascribed_g)
in (match (uu____4197) with
| (uu____4204, uu____4205, g_g) -> begin
(

let g_g1 = (

let not_p = (

let uu____4211 = (

let uu____4216 = (

let uu____4217 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.not_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____4217 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____4218 = (

let uu____4219 = (FStar_All.pipe_right p_t FStar_Syntax_Syntax.as_arg)
in (uu____4219)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____4216 uu____4218)))
in (uu____4211 FStar_Pervasives_Native.None r))
in (

let uu____4252 = (FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (not_p)))
in (FStar_TypeChecker_Env.imp_guard uu____4252 g_g)))
in (FStar_TypeChecker_Rel.force_trivial_guard env g_g1))
end));
))
end));
)
end))
end))
end))
end))
end)));
(

let tc_action = (fun env act -> (

let env01 = env
in (

let r = act.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos
in ((match ((Prims.op_disEquality (FStar_List.length act.FStar_Syntax_Syntax.action_params) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____4276 = (

let uu____4282 = (

let uu____4284 = (FStar_Syntax_Print.binders_to_string "; " act.FStar_Syntax_Syntax.action_params)
in (FStar_Util.format3 "Action %s:%s has non-empty action params (%s)" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str act.FStar_Syntax_Syntax.action_name.FStar_Ident.str uu____4284))
in ((FStar_Errors.Fatal_MalformedActionDeclaration), (uu____4282)))
in (FStar_Errors.raise_error uu____4276 r))
end
| uu____4289 -> begin
()
end);
(

let uu____4291 = (

let uu____4296 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____4296) with
| (usubst, us) -> begin
(

let uu____4319 = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____4320 = (

let uu___415_4321 = act
in (

let uu____4322 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____4323 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___415_4321.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___415_4321.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = us; FStar_Syntax_Syntax.action_params = uu___415_4321.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____4322; FStar_Syntax_Syntax.action_typ = uu____4323})))
in ((uu____4319), (uu____4320))))
end))
in (match (uu____4291) with
| (env1, act1) -> begin
(

let act_typ = (

let uu____4327 = (

let uu____4328 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____4328.FStar_Syntax_Syntax.n)
in (match (uu____4327) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____4354 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name ed.FStar_Syntax_Syntax.mname)
in (match (uu____4354) with
| true -> begin
(

let repr_ts = (

let uu____4358 = repr
in (match (uu____4358) with
| (us, t, uu____4373) -> begin
((us), (t))
end))
in (

let repr1 = (

let uu____4391 = (FStar_TypeChecker_Env.inst_tscheme_with repr_ts ct.FStar_Syntax_Syntax.comp_univs)
in (FStar_All.pipe_right uu____4391 FStar_Pervasives_Native.snd))
in (

let repr2 = (

let uu____4403 = (

let uu____4408 = (

let uu____4409 = (FStar_Syntax_Syntax.as_arg ct.FStar_Syntax_Syntax.result_typ)
in (uu____4409)::ct.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app repr1 uu____4408))
in (uu____4403 FStar_Pervasives_Native.None r))
in (

let c1 = (

let uu____4427 = (

let uu____4430 = (FStar_TypeChecker_Env.new_u_univ ())
in FStar_Pervasives_Native.Some (uu____4430))
in (FStar_Syntax_Syntax.mk_Total' repr2 uu____4427))
in (FStar_Syntax_Util.arrow bs c1)))))
end
| uu____4431 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____4433 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____4434 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act_typ)
in (match (uu____4434) with
| (act_typ1, uu____4442, g_t) -> begin
(

let uu____4444 = (

let uu____4451 = (

let uu___440_4452 = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___440_4452.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___440_4452.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___440_4452.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___440_4452.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___440_4452.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___440_4452.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___440_4452.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___440_4452.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___440_4452.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___440_4452.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___440_4452.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___440_4452.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___440_4452.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___440_4452.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___440_4452.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___440_4452.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___440_4452.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___440_4452.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___440_4452.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___440_4452.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___440_4452.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___440_4452.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___440_4452.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___440_4452.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___440_4452.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___440_4452.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___440_4452.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___440_4452.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___440_4452.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___440_4452.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___440_4452.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___440_4452.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___440_4452.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___440_4452.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___440_4452.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___440_4452.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___440_4452.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___440_4452.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___440_4452.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___440_4452.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___440_4452.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___440_4452.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___440_4452.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___440_4452.FStar_TypeChecker_Env.erasable_types_tab})
in (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____4451 act1.FStar_Syntax_Syntax.action_defn))
in (match (uu____4444) with
| (act_defn, uu____4455, g_d) -> begin
((

let uu____4458 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____4458) with
| true -> begin
(

let uu____4463 = (FStar_Syntax_Print.term_to_string act_defn)
in (

let uu____4465 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print2 "Typechecked action definition: %s and action type: %s\n" uu____4463 uu____4465)))
end
| uu____4468 -> begin
()
end));
(

let uu____4470 = (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 act_typ1)
in (

let uu____4478 = (

let uu____4479 = (FStar_Syntax_Subst.compress act_typ2)
in uu____4479.FStar_Syntax_Syntax.n)
in (match (uu____4478) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____4489) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 bs1)
in (

let uu____4512 = (FStar_Syntax_Util.type_u ())
in (match (uu____4512) with
| (t, u) -> begin
(

let reason = (FStar_Util.format2 "implicit for return type of action %s:%s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str act1.FStar_Syntax_Syntax.action_name.FStar_Ident.str)
in (

let uu____4528 = (FStar_TypeChecker_Util.new_implicit_var reason r env2 t)
in (match (uu____4528) with
| (a_tm, uu____4548, g_tm) -> begin
(

let uu____4562 = (fresh_repr r env2 u a_tm)
in (match (uu____4562) with
| (repr1, g) -> begin
(

let uu____4575 = (

let uu____4578 = (

let uu____4581 = (

let uu____4584 = (FStar_TypeChecker_Env.new_u_univ ())
in (FStar_All.pipe_right uu____4584 (fun _4587 -> FStar_Pervasives_Native.Some (_4587))))
in (FStar_Syntax_Syntax.mk_Total' repr1 uu____4581))
in (FStar_Syntax_Util.arrow bs1 uu____4578))
in (

let uu____4588 = (FStar_TypeChecker_Env.conj_guard g g_tm)
in ((uu____4575), (uu____4588))))
end))
end)))
end))))
end
| uu____4591 -> begin
(

let uu____4592 = (

let uu____4598 = (

let uu____4600 = (FStar_Syntax_Print.term_to_string act_typ2)
in (FStar_Util.format3 "Unexpected non-function type for action %s:%s (%s)" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str act1.FStar_Syntax_Syntax.action_name.FStar_Ident.str uu____4600))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____4598)))
in (FStar_Errors.raise_error uu____4592 r))
end)))
in (match (uu____4470) with
| (k, g_k) -> begin
((

let uu____4617 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____4617) with
| true -> begin
(

let uu____4622 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print1 "Expected action type: %s\n" uu____4622))
end
| uu____4625 -> begin
()
end));
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ1 k)
in ((FStar_List.iter (FStar_TypeChecker_Rel.force_trivial_guard env1) ((g_t)::(g_d)::(g_k)::(g)::[]));
(

let uu____4630 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____4630) with
| true -> begin
(

let uu____4635 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print1 "Expected action type after unification: %s\n" uu____4635))
end
| uu____4638 -> begin
()
end));
(

let act_typ2 = (

let err_msg = (fun t -> (

let uu____4648 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str act1.FStar_Syntax_Syntax.action_name.FStar_Ident.str uu____4648)))
in (

let repr_args = (fun t -> (

let uu____4669 = (

let uu____4670 = (FStar_Syntax_Subst.compress t)
in uu____4670.FStar_Syntax_Syntax.n)
in (match (uu____4669) with
| FStar_Syntax_Syntax.Tm_app (head1, (a)::is) -> begin
(

let uu____4722 = (

let uu____4723 = (FStar_Syntax_Subst.compress head1)
in uu____4723.FStar_Syntax_Syntax.n)
in (match (uu____4722) with
| FStar_Syntax_Syntax.Tm_uinst (uu____4732, us) -> begin
((us), ((FStar_Pervasives_Native.fst a)), (is))
end
| uu____4742 -> begin
(

let uu____4743 = (

let uu____4749 = (err_msg t)
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____4749)))
in (FStar_Errors.raise_error uu____4743 r))
end))
end
| uu____4758 -> begin
(

let uu____4759 = (

let uu____4765 = (err_msg t)
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____4765)))
in (FStar_Errors.raise_error uu____4759 r))
end)))
in (

let k1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 k)
in (

let uu____4775 = (

let uu____4776 = (FStar_Syntax_Subst.compress k1)
in uu____4776.FStar_Syntax_Syntax.n)
in (match (uu____4775) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4801 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4801) with
| (bs1, c1) -> begin
(

let uu____4808 = (repr_args (FStar_Syntax_Util.comp_result c1))
in (match (uu____4808) with
| (us, a, is) -> begin
(

let ct = {FStar_Syntax_Syntax.comp_univs = us; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = is; FStar_Syntax_Syntax.flags = []}
in (

let uu____4819 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_Syntax_Util.arrow bs1 uu____4819)))
end))
end))
end
| uu____4822 -> begin
(

let uu____4823 = (

let uu____4829 = (err_msg k1)
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____4829)))
in (FStar_Errors.raise_error uu____4823 r))
end)))))
in ((

let uu____4833 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____4833) with
| true -> begin
(

let uu____4838 = (FStar_Syntax_Print.term_to_string act_typ2)
in (FStar_Util.print1 "Action type after injecting it into the monad: %s\n" uu____4838))
end
| uu____4841 -> begin
()
end));
(

let act2 = (

let uu____4844 = (FStar_TypeChecker_Util.generalize_universes env1 act_defn)
in (match (uu____4844) with
| (us, act_defn1) -> begin
(match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(

let uu___513_4858 = act1
in (

let uu____4859 = (FStar_Syntax_Subst.close_univ_vars us act_typ2)
in {FStar_Syntax_Syntax.action_name = uu___513_4858.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___513_4858.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = us; FStar_Syntax_Syntax.action_params = uu___513_4858.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn1; FStar_Syntax_Syntax.action_typ = uu____4859}))
end
| uu____4860 -> begin
(

let uu____4862 = ((Prims.op_Equality (FStar_List.length us) (FStar_List.length act1.FStar_Syntax_Syntax.action_univs)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____4869 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____4869 (Prims.parse_int "0")))) us act1.FStar_Syntax_Syntax.action_univs))
in (match (uu____4862) with
| true -> begin
(

let uu___518_4874 = act1
in (

let uu____4875 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_typ2)
in {FStar_Syntax_Syntax.action_name = uu___518_4874.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___518_4874.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___518_4874.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___518_4874.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn1; FStar_Syntax_Syntax.action_typ = uu____4875}))
end
| uu____4876 -> begin
(

let uu____4878 = (

let uu____4884 = (

let uu____4886 = (FStar_Syntax_Print.univ_names_to_string us)
in (

let uu____4888 = (FStar_Syntax_Print.univ_names_to_string act1.FStar_Syntax_Syntax.action_univs)
in (FStar_Util.format4 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str act1.FStar_Syntax_Syntax.action_name.FStar_Ident.str uu____4886 uu____4888)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____4884)))
in (FStar_Errors.raise_error uu____4878 r))
end))
end)
end))
in act2);
));
));
)
end));
)
end))
end)))
end));
))))
in (

let tschemes_of = (fun uu____4913 -> (match (uu____4913) with
| (us, t, ty) -> begin
((((us), (t))), (((us), (ty))))
end))
in (

let combinators = (

let uu____4958 = (

let uu____4959 = (tschemes_of repr)
in (

let uu____4964 = (tschemes_of return_repr)
in (

let uu____4969 = (tschemes_of bind_repr)
in (

let uu____4974 = (tschemes_of stronger_repr)
in (

let uu____4979 = (tschemes_of if_then_else1)
in {FStar_Syntax_Syntax.l_base_effect = underlying_effect_lid; FStar_Syntax_Syntax.l_repr = uu____4959; FStar_Syntax_Syntax.l_return = uu____4964; FStar_Syntax_Syntax.l_bind = uu____4969; FStar_Syntax_Syntax.l_subcomp = uu____4974; FStar_Syntax_Syntax.l_if_then_else = uu____4979})))))
in FStar_Syntax_Syntax.Layered_eff (uu____4958))
in (

let uu___527_4984 = ed
in (

let uu____4985 = (FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.mname = uu___527_4984.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___527_4984.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = uu___527_4984.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___527_4984.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = (

let uu____4992 = signature
in (match (uu____4992) with
| (us, t, uu____5007) -> begin
((us), (t))
end)); FStar_Syntax_Syntax.combinators = combinators; FStar_Syntax_Syntax.actions = uu____4985; FStar_Syntax_Syntax.eff_attrs = uu___527_4984.FStar_Syntax_Syntax.eff_attrs})))));
));
));
));
))));
)
end));
))))));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____5040 = (FStar_TypeChecker_TcTerm.tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____5040)))


let tc_non_layered_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed _quals -> ((

let uu____5062 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____5062) with
| true -> begin
(

let uu____5067 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5067))
end
| uu____5071 -> begin
()
end));
(

let uu____5073 = (

let uu____5078 = (FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs)
in (match (uu____5078) with
| (ed_univs_subst, ed_univs) -> begin
(

let bs = (

let uu____5102 = (FStar_Syntax_Subst.subst_binders ed_univs_subst ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_binders uu____5102))
in (

let uu____5103 = (

let uu____5110 = (FStar_TypeChecker_Env.push_univ_vars env0 ed_univs)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____5110 bs))
in (match (uu____5103) with
| (bs1, uu____5116, uu____5117) -> begin
(

let uu____5118 = (

let tmp_t = (

let uu____5128 = (

let uu____5131 = (FStar_All.pipe_right FStar_Syntax_Syntax.U_zero (fun _5136 -> FStar_Pervasives_Native.Some (_5136)))
in (FStar_Syntax_Syntax.mk_Total' FStar_Syntax_Syntax.t_unit uu____5131))
in (FStar_Syntax_Util.arrow bs1 uu____5128))
in (

let uu____5137 = (FStar_TypeChecker_Util.generalize_universes env0 tmp_t)
in (match (uu____5137) with
| (us, tmp_t1) -> begin
(

let uu____5154 = (

let uu____5155 = (

let uu____5156 = (FStar_All.pipe_right tmp_t1 FStar_Syntax_Util.arrow_formals)
in (FStar_All.pipe_right uu____5156 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5155 FStar_Syntax_Subst.close_binders))
in ((us), (uu____5154)))
end)))
in (match (uu____5118) with
| (us, bs2) -> begin
(match (ed_univs) with
| [] -> begin
((us), (bs2))
end
| uu____5193 -> begin
(

let uu____5196 = ((Prims.op_Equality (FStar_List.length ed_univs) (FStar_List.length us)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____5203 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____5203 (Prims.parse_int "0")))) ed_univs us))
in (match (uu____5196) with
| true -> begin
((us), (bs2))
end
| uu____5212 -> begin
(

let uu____5214 = (

let uu____5220 = (

let uu____5222 = (FStar_Util.string_of_int (FStar_List.length ed_univs))
in (

let uu____5224 = (FStar_Util.string_of_int (FStar_List.length us))
in (FStar_Util.format3 "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s" ed.FStar_Syntax_Syntax.mname.FStar_Ident.str uu____5222 uu____5224)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____5220)))
in (

let uu____5228 = (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)
in (FStar_Errors.raise_error uu____5214 uu____5228)))
end))
end)
end))
end)))
end))
in (match (uu____5073) with
| (us, bs) -> begin
(

let ed1 = (

let uu___564_5236 = ed
in {FStar_Syntax_Syntax.mname = uu___564_5236.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___564_5236.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = us; FStar_Syntax_Syntax.binders = bs; FStar_Syntax_Syntax.signature = uu___564_5236.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.combinators = uu___564_5236.FStar_Syntax_Syntax.combinators; FStar_Syntax_Syntax.actions = uu___564_5236.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___564_5236.FStar_Syntax_Syntax.eff_attrs})
in (

let uu____5237 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5237) with
| (ed_univs_subst, ed_univs) -> begin
(

let uu____5256 = (

let uu____5261 = (FStar_Syntax_Subst.subst_binders ed_univs_subst bs)
in (FStar_Syntax_Subst.open_binders' uu____5261))
in (match (uu____5256) with
| (ed_bs, ed_bs_subst) -> begin
(

let ed2 = (

let op = (fun uu____5282 -> (match (uu____5282) with
| (us1, t) -> begin
(

let t1 = (

let uu____5302 = (FStar_Syntax_Subst.shift_subst ((FStar_List.length ed_bs) + (FStar_List.length us1)) ed_univs_subst)
in (FStar_Syntax_Subst.subst uu____5302 t))
in (

let uu____5311 = (

let uu____5312 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us1) ed_bs_subst)
in (FStar_Syntax_Subst.subst uu____5312 t1))
in ((us1), (uu____5311))))
end))
in (

let uu___578_5317 = ed1
in (

let uu____5318 = (op ed1.FStar_Syntax_Syntax.signature)
in (

let uu____5319 = (FStar_Syntax_Util.apply_eff_combinators op ed1.FStar_Syntax_Syntax.combinators)
in (

let uu____5320 = (FStar_List.map (fun a -> (

let uu___581_5328 = a
in (

let uu____5329 = (

let uu____5330 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____5330))
in (

let uu____5341 = (

let uu____5342 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____5342))
in {FStar_Syntax_Syntax.action_name = uu___581_5328.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___581_5328.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___581_5328.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___581_5328.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____5329; FStar_Syntax_Syntax.action_typ = uu____5341})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.mname = uu___578_5317.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___578_5317.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = uu___578_5317.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___578_5317.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu____5318; FStar_Syntax_Syntax.combinators = uu____5319; FStar_Syntax_Syntax.actions = uu____5320; FStar_Syntax_Syntax.eff_attrs = uu___578_5317.FStar_Syntax_Syntax.eff_attrs})))))
in ((

let uu____5354 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____5354) with
| true -> begin
(

let uu____5359 = (FStar_Syntax_Print.eff_decl_to_string false ed2)
in (FStar_Util.print1 "After typechecking binders eff_decl: \n\t%s\n" uu____5359))
end
| uu____5363 -> begin
()
end));
(

let env = (

let uu____5366 = (FStar_TypeChecker_Env.push_univ_vars env0 ed_univs)
in (FStar_TypeChecker_Env.push_binders uu____5366 ed_bs))
in (

let check_and_gen' = (fun comb n1 env_opt uu____5401 k -> (match (uu____5401) with
| (us1, t) -> begin
(

let env1 = (match ((FStar_Util.is_some env_opt)) with
| true -> begin
(FStar_All.pipe_right env_opt FStar_Util.must)
end
| uu____5419 -> begin
env
end)
in (

let uu____5421 = (FStar_Syntax_Subst.open_univ_vars us1 t)
in (match (uu____5421) with
| (us2, t1) -> begin
(

let t2 = (match (k) with
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____5430 = (FStar_TypeChecker_Env.push_univ_vars env1 us2)
in (FStar_TypeChecker_TcTerm.tc_check_trivial_guard uu____5430 t1 k1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5431 = (

let uu____5438 = (FStar_TypeChecker_Env.push_univ_vars env1 us2)
in (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____5438 t1))
in (match (uu____5431) with
| (t2, uu____5440, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
t2;
)
end))
end)
in (

let uu____5443 = (FStar_TypeChecker_Util.generalize_universes env1 t2)
in (match (uu____5443) with
| (g_us, t3) -> begin
((match ((Prims.op_disEquality (FStar_List.length g_us) n1)) with
| true -> begin
(

let error = (

let uu____5459 = (FStar_Util.string_of_int n1)
in (

let uu____5461 = (

let uu____5463 = (FStar_All.pipe_right g_us FStar_List.length)
in (FStar_All.pipe_right uu____5463 FStar_Util.string_of_int))
in (FStar_Util.format4 "Expected %s:%s to be universe-polymorphic in %s universes, found %s" ed2.FStar_Syntax_Syntax.mname.FStar_Ident.str comb uu____5459 uu____5461)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (error)) t3.FStar_Syntax_Syntax.pos))
end
| uu____5472 -> begin
()
end);
(match (us2) with
| [] -> begin
((g_us), (t3))
end
| uu____5478 -> begin
(

let uu____5479 = ((Prims.op_Equality (FStar_List.length us2) (FStar_List.length g_us)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____5486 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____5486 (Prims.parse_int "0")))) us2 g_us))
in (match (uu____5479) with
| true -> begin
((g_us), (t3))
end
| uu____5495 -> begin
(

let uu____5497 = (

let uu____5503 = (

let uu____5505 = (FStar_Util.string_of_int (FStar_List.length us2))
in (

let uu____5507 = (FStar_Util.string_of_int (FStar_List.length g_us))
in (FStar_Util.format4 "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s" ed2.FStar_Syntax_Syntax.mname.FStar_Ident.str comb uu____5505 uu____5507)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____5503)))
in (FStar_Errors.raise_error uu____5497 t3.FStar_Syntax_Syntax.pos))
end))
end);
)
end)))
end)))
end))
in (

let signature = (check_and_gen' "signature" (Prims.parse_int "1") FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature FStar_Pervasives_Native.None)
in ((

let uu____5515 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____5515) with
| true -> begin
(

let uu____5520 = (FStar_Syntax_Print.tscheme_to_string signature)
in (FStar_Util.print1 "Typechecked signature: %s\n" uu____5520))
end
| uu____5523 -> begin
()
end));
(

let fresh_a_and_wp = (fun uu____5536 -> (

let fail1 = (fun t -> (

let uu____5549 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env ed2.FStar_Syntax_Syntax.mname t)
in (FStar_Errors.raise_error uu____5549 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)))
in (

let uu____5565 = (FStar_TypeChecker_Env.inst_tscheme signature)
in (match (uu____5565) with
| (uu____5576, signature1) -> begin
(

let uu____5578 = (

let uu____5579 = (FStar_Syntax_Subst.compress signature1)
in uu____5579.FStar_Syntax_Syntax.n)
in (match (uu____5578) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, uu____5589) -> begin
(

let bs2 = (FStar_Syntax_Subst.open_binders bs1)
in (match (bs2) with
| ((a, uu____5618))::((wp, uu____5620))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____5649 -> begin
(fail1 signature1)
end))
end
| uu____5650 -> begin
(fail1 signature1)
end))
end))))
in (

let log_combinator = (fun s ts -> (

let uu____5664 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))
in (match (uu____5664) with
| true -> begin
(

let uu____5669 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.print3 "Typechecked %s:%s = %s\n" ed2.FStar_Syntax_Syntax.mname.FStar_Ident.str s uu____5669))
end
| uu____5672 -> begin
()
end)))
in (

let ret_wp = (

let uu____5675 = (fresh_a_and_wp ())
in (match (uu____5675) with
| (a, wp_sort) -> begin
(

let k = (

let uu____5691 = (

let uu____5700 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5707 = (

let uu____5716 = (

let uu____5723 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____5723))
in (uu____5716)::[])
in (uu____5700)::uu____5707))
in (

let uu____5742 = (FStar_Syntax_Syntax.mk_GTotal wp_sort)
in (FStar_Syntax_Util.arrow uu____5691 uu____5742)))
in (

let uu____5745 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_return_vc_combinator)
in (check_and_gen' "ret_wp" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____5745 (FStar_Pervasives_Native.Some (k)))))
end))
in ((log_combinator "ret_wp" ret_wp);
(

let bind_wp = (

let uu____5759 = (fresh_a_and_wp ())
in (match (uu____5759) with
| (a, wp_sort_a) -> begin
(

let uu____5772 = (fresh_a_and_wp ())
in (match (uu____5772) with
| (b, wp_sort_b) -> begin
(

let wp_sort_a_b = (

let uu____5788 = (

let uu____5797 = (

let uu____5804 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____5804))
in (uu____5797)::[])
in (

let uu____5817 = (FStar_Syntax_Syntax.mk_Total wp_sort_b)
in (FStar_Syntax_Util.arrow uu____5788 uu____5817)))
in (

let k = (

let uu____5823 = (

let uu____5832 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____5839 = (

let uu____5848 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5855 = (

let uu____5864 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____5871 = (

let uu____5880 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (

let uu____5887 = (

let uu____5896 = (FStar_Syntax_Syntax.null_binder wp_sort_a_b)
in (uu____5896)::[])
in (uu____5880)::uu____5887))
in (uu____5864)::uu____5871))
in (uu____5848)::uu____5855))
in (uu____5832)::uu____5839))
in (

let uu____5939 = (FStar_Syntax_Syntax.mk_Total wp_sort_b)
in (FStar_Syntax_Util.arrow uu____5823 uu____5939)))
in (

let uu____5942 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_bind_vc_combinator)
in (check_and_gen' "bind_wp" (Prims.parse_int "2") FStar_Pervasives_Native.None uu____5942 (FStar_Pervasives_Native.Some (k))))))
end))
end))
in ((log_combinator "bind_wp" bind_wp);
(

let stronger = (

let uu____5956 = (fresh_a_and_wp ())
in (match (uu____5956) with
| (a, wp_sort_a) -> begin
(

let uu____5969 = (FStar_Syntax_Util.type_u ())
in (match (uu____5969) with
| (t, uu____5975) -> begin
(

let k = (

let uu____5979 = (

let uu____5988 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5995 = (

let uu____6004 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (

let uu____6011 = (

let uu____6020 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (uu____6020)::[])
in (uu____6004)::uu____6011))
in (uu____5988)::uu____5995))
in (

let uu____6051 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____5979 uu____6051)))
in (

let uu____6054 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_stronger_vc_combinator)
in (check_and_gen' "stronger" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____6054 (FStar_Pervasives_Native.Some (k)))))
end))
end))
in ((log_combinator "stronger" stronger);
(

let if_then_else1 = (

let uu____6068 = (fresh_a_and_wp ())
in (match (uu____6068) with
| (a, wp_sort_a) -> begin
(

let p = (

let uu____6082 = (

let uu____6085 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____6085))
in (

let uu____6086 = (

let uu____6087 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6087 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____6082 uu____6086)))
in (

let k = (

let uu____6099 = (

let uu____6108 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6115 = (

let uu____6124 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____6131 = (

let uu____6140 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (

let uu____6147 = (

let uu____6156 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (uu____6156)::[])
in (uu____6140)::uu____6147))
in (uu____6124)::uu____6131))
in (uu____6108)::uu____6115))
in (

let uu____6193 = (FStar_Syntax_Syntax.mk_Total wp_sort_a)
in (FStar_Syntax_Util.arrow uu____6099 uu____6193)))
in (

let uu____6196 = (

let uu____6201 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_wp_if_then_else_combinator)
in (FStar_All.pipe_right uu____6201 FStar_Util.must))
in (check_and_gen' "if_then_else" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____6196 (FStar_Pervasives_Native.Some (k))))))
end))
in ((log_combinator "if_then_else" if_then_else1);
(

let ite_wp = (

let uu____6233 = (fresh_a_and_wp ())
in (match (uu____6233) with
| (a, wp_sort_a) -> begin
(

let k = (

let uu____6249 = (

let uu____6258 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6265 = (

let uu____6274 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (uu____6274)::[])
in (uu____6258)::uu____6265))
in (

let uu____6299 = (FStar_Syntax_Syntax.mk_Total wp_sort_a)
in (FStar_Syntax_Util.arrow uu____6249 uu____6299)))
in (

let uu____6302 = (

let uu____6307 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_wp_ite_combinator)
in (FStar_All.pipe_right uu____6307 FStar_Util.must))
in (check_and_gen' "ite_wp" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____6302 (FStar_Pervasives_Native.Some (k)))))
end))
in ((log_combinator "ite_wp" ite_wp);
(

let close_wp = (

let uu____6323 = (fresh_a_and_wp ())
in (match (uu____6323) with
| (a, wp_sort_a) -> begin
(

let b = (

let uu____6337 = (

let uu____6340 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____6340))
in (

let uu____6341 = (

let uu____6342 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6342 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____6337 uu____6341)))
in (

let wp_sort_b_a = (

let uu____6354 = (

let uu____6363 = (

let uu____6370 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____6370))
in (uu____6363)::[])
in (

let uu____6383 = (FStar_Syntax_Syntax.mk_Total wp_sort_a)
in (FStar_Syntax_Util.arrow uu____6354 uu____6383)))
in (

let k = (

let uu____6389 = (

let uu____6398 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6405 = (

let uu____6414 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____6421 = (

let uu____6430 = (FStar_Syntax_Syntax.null_binder wp_sort_b_a)
in (uu____6430)::[])
in (uu____6414)::uu____6421))
in (uu____6398)::uu____6405))
in (

let uu____6461 = (FStar_Syntax_Syntax.mk_Total wp_sort_a)
in (FStar_Syntax_Util.arrow uu____6389 uu____6461)))
in (

let uu____6464 = (

let uu____6469 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_wp_close_combinator)
in (FStar_All.pipe_right uu____6469 FStar_Util.must))
in (check_and_gen' "close_wp" (Prims.parse_int "2") FStar_Pervasives_Native.None uu____6464 (FStar_Pervasives_Native.Some (k)))))))
end))
in ((log_combinator "close_wp" close_wp);
(

let trivial = (

let uu____6485 = (fresh_a_and_wp ())
in (match (uu____6485) with
| (a, wp_sort_a) -> begin
(

let uu____6498 = (FStar_Syntax_Util.type_u ())
in (match (uu____6498) with
| (t, uu____6504) -> begin
(

let k = (

let uu____6508 = (

let uu____6517 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6524 = (

let uu____6533 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (uu____6533)::[])
in (uu____6517)::uu____6524))
in (

let uu____6558 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____6508 uu____6558)))
in (

let trivial = (

let uu____6562 = (

let uu____6567 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_wp_trivial_combinator)
in (FStar_All.pipe_right uu____6567 FStar_Util.must))
in (check_and_gen' "trivial" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____6562 (FStar_Pervasives_Native.Some (k))))
in ((log_combinator "trivial" trivial);
trivial;
)))
end))
end))
in (

let uu____6582 = (

let uu____6599 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_eff_repr)
in (match (uu____6599) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____6628 -> begin
(

let repr = (

let uu____6632 = (fresh_a_and_wp ())
in (match (uu____6632) with
| (a, wp_sort_a) -> begin
(

let uu____6645 = (FStar_Syntax_Util.type_u ())
in (match (uu____6645) with
| (t, uu____6651) -> begin
(

let k = (

let uu____6655 = (

let uu____6664 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6671 = (

let uu____6680 = (FStar_Syntax_Syntax.null_binder wp_sort_a)
in (uu____6680)::[])
in (uu____6664)::uu____6671))
in (

let uu____6705 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____6655 uu____6705)))
in (

let uu____6708 = (

let uu____6713 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_eff_repr)
in (FStar_All.pipe_right uu____6713 FStar_Util.must))
in (check_and_gen' "repr" (Prims.parse_int "1") FStar_Pervasives_Native.None uu____6708 (FStar_Pervasives_Native.Some (k)))))
end))
end))
in ((log_combinator "repr" repr);
(

let mk_repr' = (fun t wp -> (

let uu____6757 = (FStar_TypeChecker_Env.inst_tscheme repr)
in (match (uu____6757) with
| (uu____6764, repr1) -> begin
(

let repr2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env repr1)
in (

let uu____6767 = (

let uu____6774 = (

let uu____6775 = (

let uu____6792 = (

let uu____6803 = (FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg)
in (

let uu____6820 = (

let uu____6831 = (FStar_All.pipe_right wp FStar_Syntax_Syntax.as_arg)
in (uu____6831)::[])
in (uu____6803)::uu____6820))
in ((repr2), (uu____6792)))
in FStar_Syntax_Syntax.Tm_app (uu____6775))
in (FStar_Syntax_Syntax.mk uu____6774))
in (uu____6767 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
end)))
in (

let mk_repr = (fun a wp -> (

let uu____6897 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' uu____6897 wp)))
in (

let destruct_repr = (fun t -> (

let uu____6912 = (

let uu____6913 = (FStar_Syntax_Subst.compress t)
in uu____6913.FStar_Syntax_Syntax.n)
in (match (uu____6912) with
| FStar_Syntax_Syntax.Tm_app (uu____6924, ((t1, uu____6926))::((wp, uu____6928))::[]) -> begin
((t1), (wp))
end
| uu____6987 -> begin
(failwith "Unexpected repr type")
end)))
in (

let return_repr = (

let return_repr_ts = (

let uu____7003 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_return_repr)
in (FStar_All.pipe_right uu____7003 FStar_Util.must))
in (

let uu____7030 = (fresh_a_and_wp ())
in (match (uu____7030) with
| (a, uu____7038) -> begin
(

let x_a = (

let uu____7044 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____7044))
in (

let res = (

let wp = (

let uu____7052 = (

let uu____7057 = (

let uu____7058 = (FStar_TypeChecker_Env.inst_tscheme ret_wp)
in (FStar_All.pipe_right uu____7058 FStar_Pervasives_Native.snd))
in (

let uu____7067 = (

let uu____7068 = (

let uu____7077 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_All.pipe_right uu____7077 FStar_Syntax_Syntax.as_arg))
in (

let uu____7086 = (

let uu____7097 = (

let uu____7106 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_right uu____7106 FStar_Syntax_Syntax.as_arg))
in (uu____7097)::[])
in (uu____7068)::uu____7086))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7057 uu____7067)))
in (uu____7052 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let k = (

let uu____7142 = (

let uu____7151 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____7158 = (

let uu____7167 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____7167)::[])
in (uu____7151)::uu____7158))
in (

let uu____7192 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____7142 uu____7192)))
in (

let uu____7195 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____7195) with
| (k1, uu____7203, uu____7204) -> begin
(

let env1 = (

let uu____7208 = (FStar_TypeChecker_Env.set_range env (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____7208))
in (check_and_gen' "return_repr" (Prims.parse_int "1") env1 return_repr_ts (FStar_Pervasives_Native.Some (k1))))
end)))))
end)))
in ((log_combinator "return_repr" return_repr);
(

let bind_repr = (

let bind_repr_ts = (

let uu____7221 = (FStar_All.pipe_right ed2 FStar_Syntax_Util.get_bind_repr)
in (FStar_All.pipe_right uu____7221 FStar_Util.must))
in (

let r = (

let uu____7259 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____7259 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____7260 = (fresh_a_and_wp ())
in (match (uu____7260) with
| (a, wp_sort_a) -> begin
(

let uu____7273 = (fresh_a_and_wp ())
in (match (uu____7273) with
| (b, wp_sort_b) -> begin
(

let wp_sort_a_b = (

let uu____7289 = (

let uu____7298 = (

let uu____7305 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____7305))
in (uu____7298)::[])
in (

let uu____7318 = (FStar_Syntax_Syntax.mk_Total wp_sort_b)
in (FStar_Syntax_Util.arrow uu____7289 uu____7318)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_sort_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None wp_sort_a_b)
in (

let x_a = (

let uu____7326 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____7326))
in (

let wp_g_x = (

let uu____7331 = (

let uu____7336 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____7337 = (

let uu____7338 = (

let uu____7347 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_right uu____7347 FStar_Syntax_Syntax.as_arg))
in (uu____7338)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7336 uu____7337)))
in (uu____7331 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____7378 = (

let uu____7383 = (

let uu____7384 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____7384 FStar_Pervasives_Native.snd))
in (

let uu____7393 = (

let uu____7394 = (

let uu____7397 = (

let uu____7400 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____7401 = (

let uu____7404 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____7405 = (

let uu____7408 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____7409 = (

let uu____7412 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____7412)::[])
in (uu____7408)::uu____7409))
in (uu____7404)::uu____7405))
in (uu____7400)::uu____7401))
in (r)::uu____7397)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____7394))
in (FStar_Syntax_Syntax.mk_Tm_app uu____7383 uu____7393)))
in (uu____7378 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____7430 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____7430) with
| true -> begin
(

let uu____7441 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____7448 = (

let uu____7457 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____7457)::[])
in (uu____7441)::uu____7448))
end
| uu____7482 -> begin
[]
end))
in (

let k = (

let uu____7493 = (

let uu____7502 = (

let uu____7511 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____7518 = (

let uu____7527 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____7527)::[])
in (uu____7511)::uu____7518))
in (

let uu____7552 = (

let uu____7561 = (

let uu____7570 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____7577 = (

let uu____7586 = (

let uu____7593 = (

let uu____7594 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____7594))
in (FStar_Syntax_Syntax.null_binder uu____7593))
in (

let uu____7595 = (

let uu____7604 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____7611 = (

let uu____7620 = (

let uu____7627 = (

let uu____7628 = (

let uu____7637 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____7637)::[])
in (

let uu____7656 = (

let uu____7659 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____7659))
in (FStar_Syntax_Util.arrow uu____7628 uu____7656)))
in (FStar_Syntax_Syntax.null_binder uu____7627))
in (uu____7620)::[])
in (uu____7604)::uu____7611))
in (uu____7586)::uu____7595))
in (uu____7570)::uu____7577))
in (FStar_List.append maybe_range_arg uu____7561))
in (FStar_List.append uu____7502 uu____7552)))
in (

let uu____7704 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____7493 uu____7704)))
in (

let uu____7707 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____7707) with
| (k1, uu____7715, uu____7716) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos)
in (

let env2 = (FStar_All.pipe_right (

let uu___776_7726 = env1
in {FStar_TypeChecker_Env.solver = uu___776_7726.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___776_7726.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___776_7726.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___776_7726.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___776_7726.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___776_7726.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___776_7726.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___776_7726.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___776_7726.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___776_7726.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___776_7726.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___776_7726.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___776_7726.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___776_7726.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___776_7726.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___776_7726.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___776_7726.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___776_7726.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___776_7726.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___776_7726.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___776_7726.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___776_7726.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___776_7726.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___776_7726.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___776_7726.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___776_7726.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___776_7726.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___776_7726.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___776_7726.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___776_7726.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___776_7726.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___776_7726.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___776_7726.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___776_7726.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___776_7726.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___776_7726.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___776_7726.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___776_7726.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___776_7726.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___776_7726.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___776_7726.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___776_7726.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___776_7726.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___776_7726.FStar_TypeChecker_Env.erasable_types_tab}) (fun _7728 -> FStar_Pervasives_Native.Some (_7728)))
in (check_and_gen' "bind_repr" (Prims.parse_int "2") env2 bind_repr_ts (FStar_Pervasives_Native.Some (k1)))))
end))))))))))
end))
end))))
in ((log_combinator "bind_repr" bind_repr);
(

let actions = (

let check_action = (fun act -> ((match ((Prims.op_disEquality (FStar_List.length act.FStar_Syntax_Syntax.action_params) (Prims.parse_int "0"))) with
| true -> begin
(failwith "tc_eff_decl: expected action_params to be empty")
end
| uu____7753 -> begin
()
end);
(

let uu____7755 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
((env), (act))
end
| uu____7767 -> begin
(

let uu____7769 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____7769) with
| (usubst, uvs) -> begin
(

let uu____7792 = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (

let uu____7793 = (

let uu___789_7794 = act
in (

let uu____7795 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____7796 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___789_7794.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___789_7794.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu___789_7794.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____7795; FStar_Syntax_Syntax.action_typ = uu____7796})))
in ((uu____7792), (uu____7793))))
end))
end)
in (match (uu____7755) with
| (env1, act1) -> begin
(

let act_typ = (

let uu____7800 = (

let uu____7801 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____7801.FStar_Syntax_Syntax.n)
in (match (uu____7800) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____7827 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)
in (match (uu____7827) with
| true -> begin
(

let uu____7830 = (

let uu____7833 = (

let uu____7834 = (

let uu____7835 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____7835))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____7834))
in (FStar_Syntax_Syntax.mk_Total uu____7833))
in (FStar_Syntax_Util.arrow bs1 uu____7830))
end
| uu____7856 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____7858 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____7859 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act_typ)
in (match (uu____7859) with
| (act_typ1, uu____7867, g_t) -> begin
(

let env' = (

let uu___806_7870 = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___806_7870.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___806_7870.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___806_7870.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___806_7870.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___806_7870.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___806_7870.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___806_7870.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___806_7870.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___806_7870.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___806_7870.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___806_7870.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___806_7870.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___806_7870.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___806_7870.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___806_7870.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___806_7870.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___806_7870.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___806_7870.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___806_7870.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___806_7870.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___806_7870.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___806_7870.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___806_7870.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___806_7870.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___806_7870.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___806_7870.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___806_7870.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___806_7870.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___806_7870.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___806_7870.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___806_7870.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___806_7870.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___806_7870.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___806_7870.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___806_7870.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___806_7870.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___806_7870.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___806_7870.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___806_7870.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___806_7870.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___806_7870.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___806_7870.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___806_7870.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___806_7870.FStar_TypeChecker_Env.erasable_types_tab})
in ((

let uu____7873 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____7873) with
| true -> begin
(

let uu____7877 = (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name)
in (

let uu____7879 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____7881 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" uu____7877 uu____7879 uu____7881))))
end
| uu____7884 -> begin
()
end));
(

let uu____7886 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____7886) with
| (act_defn, uu____7894, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Beta)::[]) env1 act_typ1)
in (

let uu____7898 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c) -> begin
(

let uu____7934 = (FStar_Syntax_Subst.open_comp bs1 c)
in (match (uu____7934) with
| (bs2, uu____7946) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____7953 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs2 uu____7953))
in (

let uu____7956 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 k)
in (match (uu____7956) with
| (k1, uu____7970, g) -> begin
((k1), (g))
end))))
end))
end
| uu____7974 -> begin
(

let uu____7975 = (

let uu____7981 = (

let uu____7983 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____7985 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____7983 uu____7985)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____7981)))
in (FStar_Errors.raise_error uu____7975 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____7898) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ2 expected_k)
in ((

let uu____8003 = (

let uu____8004 = (

let uu____8005 = (FStar_TypeChecker_Env.conj_guard g_t g)
in (FStar_TypeChecker_Env.conj_guard g_k uu____8005))
in (FStar_TypeChecker_Env.conj_guard g_a uu____8004))
in (FStar_TypeChecker_Rel.force_trivial_guard env1 uu____8003));
(

let act_typ3 = (

let uu____8007 = (

let uu____8008 = (FStar_Syntax_Subst.compress expected_k)
in uu____8008.FStar_Syntax_Syntax.n)
in (match (uu____8007) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c) -> begin
(

let uu____8033 = (FStar_Syntax_Subst.open_comp bs1 c)
in (match (uu____8033) with
| (bs2, c1) -> begin
(

let uu____8040 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____8040) with
| (a, wp) -> begin
(

let c2 = (

let uu____8060 = (

let uu____8061 = (env1.FStar_TypeChecker_Env.universe_of env1 a)
in (uu____8061)::[])
in (

let uu____8062 = (

let uu____8073 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8073)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____8060; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = uu____8062; FStar_Syntax_Syntax.flags = []}))
in (

let uu____8098 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs2 uu____8098)))
end))
end))
end
| uu____8101 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____8103 = (match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env1 act_defn1)
end
| uu____8123 -> begin
(

let uu____8125 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_defn1)
in ((act1.FStar_Syntax_Syntax.action_univs), (uu____8125)))
end)
in (match (uu____8103) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___856_8144 = act1
in {FStar_Syntax_Syntax.action_name = uu___856_8144.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___856_8144.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___856_8144.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
end)));
))
end))))
end));
))
end)))
end));
))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((FStar_Pervasives_Native.Some (repr)), (FStar_Pervasives_Native.Some (return_repr)), (FStar_Pervasives_Native.Some (bind_repr)), (actions)));
));
)))));
))
end))
in (match (uu____6582) with
| (repr, return_repr, bind_repr, actions) -> begin
(

let cl = (fun ts -> (

let ts1 = (FStar_Syntax_Subst.close_tscheme ed_bs ts)
in (

let ed_univs_closing = (FStar_Syntax_Subst.univ_var_closing ed_univs)
in (

let uu____8187 = (FStar_Syntax_Subst.shift_subst (FStar_List.length ed_bs) ed_univs_closing)
in (FStar_Syntax_Subst.subst_tscheme uu____8187 ts1)))))
in (

let combinators = {FStar_Syntax_Syntax.ret_wp = ret_wp; FStar_Syntax_Syntax.bind_wp = bind_wp; FStar_Syntax_Syntax.stronger = stronger; FStar_Syntax_Syntax.if_then_else = if_then_else1; FStar_Syntax_Syntax.ite_wp = ite_wp; FStar_Syntax_Syntax.close_wp = close_wp; FStar_Syntax_Syntax.trivial = trivial; FStar_Syntax_Syntax.repr = repr; FStar_Syntax_Syntax.return_repr = return_repr; FStar_Syntax_Syntax.bind_repr = bind_repr}
in (

let combinators1 = (FStar_Syntax_Util.apply_wp_eff_combinators cl combinators)
in (

let combinators2 = (match (ed2.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (uu____8199) -> begin
FStar_Syntax_Syntax.Primitive_eff (combinators1)
end
| FStar_Syntax_Syntax.DM4F_eff (uu____8200) -> begin
FStar_Syntax_Syntax.DM4F_eff (combinators1)
end
| uu____8201 -> begin
(failwith "Impossible! tc_eff_decl on a layered effect is not expected")
end)
in (

let ed3 = (

let uu___876_8204 = ed2
in (

let uu____8205 = (cl signature)
in (

let uu____8206 = (FStar_List.map (fun a -> (

let uu___879_8214 = a
in (

let uu____8215 = (

let uu____8216 = (cl ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_All.pipe_right uu____8216 FStar_Pervasives_Native.snd))
in (

let uu____8241 = (

let uu____8242 = (cl ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_All.pipe_right uu____8242 FStar_Pervasives_Native.snd))
in {FStar_Syntax_Syntax.action_name = uu___879_8214.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___879_8214.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___879_8214.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___879_8214.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____8215; FStar_Syntax_Syntax.action_typ = uu____8241})))) actions)
in {FStar_Syntax_Syntax.mname = uu___876_8204.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___876_8204.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = uu___876_8204.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___876_8204.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu____8205; FStar_Syntax_Syntax.combinators = combinators2; FStar_Syntax_Syntax.actions = uu____8206; FStar_Syntax_Syntax.eff_attrs = uu___876_8204.FStar_Syntax_Syntax.eff_attrs})))
in ((

let uu____8268 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))
in (match (uu____8268) with
| true -> begin
(

let uu____8273 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print1 "Typechecked effect declaration:\n\t%s\n" uu____8273))
end
| uu____8277 -> begin
()
end));
ed3;
))))))
end)));
));
));
));
));
));
))));
))));
))
end))
end)))
end));
))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl = (fun env ed quals -> (

let uu____8299 = (

let uu____8314 = (FStar_All.pipe_right ed FStar_Syntax_Util.is_layered)
in (match (uu____8314) with
| true -> begin
tc_layered_eff_decl
end
| uu____8329 -> begin
tc_non_layered_eff_decl
end))
in (uu____8299 env ed quals)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail1 = (fun uu____8364 -> (

let uu____8365 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in (

let uu____8371 = (FStar_Ident.range_of_lid m)
in (FStar_Errors.raise_error uu____8365 uu____8371))))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____8415))::((wp, uu____8417))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____8446 -> begin
(fail1 ())
end))
end
| uu____8447 -> begin
(fail1 ())
end))))


let tc_layered_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sub_eff  ->  FStar_Syntax_Syntax.sub_eff = (fun env0 sub1 -> ((

let uu____8460 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____8460) with
| true -> begin
(

let uu____8465 = (FStar_Syntax_Print.sub_eff_to_string sub1)
in (FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8465))
end
| uu____8468 -> begin
()
end));
(

let uu____8470 = (FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must)
in (match (uu____8470) with
| (us, lift) -> begin
(

let r = lift.FStar_Syntax_Syntax.pos
in ((

let src_ed = (FStar_TypeChecker_Env.get_effect_decl env0 sub1.FStar_Syntax_Syntax.source)
in (

let tgt_ed = (FStar_TypeChecker_Env.get_effect_decl env0 sub1.FStar_Syntax_Syntax.target)
in (

let uu____8503 = (((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) && (

let uu____8507 = (

let uu____8508 = (FStar_All.pipe_right src_ed FStar_Syntax_Util.get_layered_effect_base)
in (FStar_All.pipe_right uu____8508 FStar_Util.must))
in (FStar_Ident.lid_equals uu____8507 tgt_ed.FStar_Syntax_Syntax.mname))) || (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) && (

let uu____8517 = (

let uu____8518 = (FStar_All.pipe_right tgt_ed FStar_Syntax_Util.get_layered_effect_base)
in (FStar_All.pipe_right uu____8518 FStar_Util.must))
in (FStar_Ident.lid_equals uu____8517 src_ed.FStar_Syntax_Syntax.mname))) && (

let uu____8526 = (FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname FStar_Parser_Const.effect_PURE_lid)
in (not (uu____8526)))))
in (match (uu____8503) with
| true -> begin
(

let uu____8529 = (

let uu____8535 = (

let uu____8537 = (FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname FStar_Ident.string_of_lid)
in (

let uu____8540 = (FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname FStar_Ident.string_of_lid)
in (FStar_Util.format2 "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)" uu____8537 uu____8540)))
in ((FStar_Errors.Fatal_EffectsCannotBeComposed), (uu____8535)))
in (FStar_Errors.raise_error uu____8529 r))
end
| uu____8545 -> begin
()
end))));
(

let uu____8547 = (match ((Prims.op_Equality (FStar_List.length us) (Prims.parse_int "0"))) with
| true -> begin
((env0), (us), (lift))
end
| uu____8569 -> begin
(

let uu____8571 = (FStar_Syntax_Subst.open_univ_vars us lift)
in (match (uu____8571) with
| (us1, lift1) -> begin
(

let uu____8586 = (FStar_TypeChecker_Env.push_univ_vars env0 us1)
in ((uu____8586), (us1), (lift1)))
end))
end)
in (match (uu____8547) with
| (env, us1, lift1) -> begin
(

let uu____8596 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1)
in (match (uu____8596) with
| (lift2, lc, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let lift_ty = (FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env0))
in ((

let uu____8609 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____8609) with
| true -> begin
(

let uu____8614 = (FStar_Syntax_Print.term_to_string lift2)
in (

let uu____8616 = (FStar_Syntax_Print.term_to_string lift_ty)
in (FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n" uu____8614 uu____8616)))
end
| uu____8619 -> begin
()
end));
(

let lift_t_shape_error = (fun s -> (

let uu____8630 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.source)
in (

let uu____8632 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.target)
in (

let uu____8634 = (FStar_Syntax_Print.term_to_string lift_ty)
in (FStar_Util.format4 "Unexpected shape of lift %s~>%s, reason:%s (t:%s)" uu____8630 uu____8632 s uu____8634)))))
in (

let uu____8637 = (

let uu____8644 = (

let uu____8649 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____8649 (fun uu____8666 -> (match (uu____8666) with
| (t, u) -> begin
(

let uu____8677 = (

let uu____8678 = (FStar_Syntax_Syntax.gen_bv "a" FStar_Pervasives_Native.None t)
in (FStar_All.pipe_right uu____8678 FStar_Syntax_Syntax.mk_binder))
in ((uu____8677), (u)))
end))))
in (match (uu____8644) with
| (a, u_a) -> begin
(

let rest_bs = (

let uu____8697 = (

let uu____8698 = (FStar_Syntax_Subst.compress lift_ty)
in uu____8698.FStar_Syntax_Syntax.n)
in (match (uu____8697) with
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____8710) when ((FStar_List.length bs) >= (Prims.parse_int "2")) -> begin
(

let uu____8738 = (FStar_Syntax_Subst.open_binders bs)
in (match (uu____8738) with
| ((a', uu____8748))::bs1 -> begin
(

let uu____8768 = (

let uu____8769 = (FStar_All.pipe_right bs1 (FStar_List.splitAt ((FStar_List.length bs1) - (Prims.parse_int "1"))))
in (FStar_All.pipe_right uu____8769 FStar_Pervasives_Native.fst))
in (

let uu____8867 = (

let uu____8880 = (

let uu____8883 = (

let uu____8884 = (

let uu____8891 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst a))
in ((a'), (uu____8891)))
in FStar_Syntax_Syntax.NT (uu____8884))
in (uu____8883)::[])
in (FStar_Syntax_Subst.subst_binders uu____8880))
in (FStar_All.pipe_right uu____8768 uu____8867)))
end))
end
| uu____8906 -> begin
(

let uu____8907 = (

let uu____8913 = (lift_t_shape_error "either not an arrow, or not enough binders")
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____8913)))
in (FStar_Errors.raise_error uu____8907 r))
end))
in (

let uu____8925 = (

let uu____8936 = (

let uu____8941 = (FStar_TypeChecker_Env.push_binders env ((a)::rest_bs))
in (

let uu____8948 = (

let uu____8949 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____8949 FStar_Syntax_Syntax.bv_to_name))
in (FStar_TypeChecker_Util.fresh_effect_repr_en uu____8941 r sub1.FStar_Syntax_Syntax.source u_a uu____8948)))
in (match (uu____8936) with
| (f_sort, g1) -> begin
(

let uu____8970 = (

let uu____8977 = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None f_sort)
in (FStar_All.pipe_right uu____8977 FStar_Syntax_Syntax.mk_binder))
in ((uu____8970), (g1)))
end))
in (match (uu____8925) with
| (f_b, g_f_b) -> begin
(

let bs = (a)::(FStar_List.append rest_bs ((f_b)::[]))
in (

let uu____9044 = (

let uu____9049 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let uu____9050 = (

let uu____9051 = (FStar_All.pipe_right a FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____9051 FStar_Syntax_Syntax.bv_to_name))
in (FStar_TypeChecker_Util.fresh_effect_repr_en uu____9049 r sub1.FStar_Syntax_Syntax.target u_a uu____9050)))
in (match (uu____9044) with
| (repr, g_repr) -> begin
(

let uu____9068 = (

let uu____9071 = (

let uu____9074 = (

let uu____9077 = (FStar_TypeChecker_Env.new_u_univ ())
in (FStar_All.pipe_right uu____9077 (fun _9080 -> FStar_Pervasives_Native.Some (_9080))))
in (FStar_Syntax_Syntax.mk_Total' repr uu____9074))
in (FStar_Syntax_Util.arrow bs uu____9071))
in (

let uu____9081 = (FStar_TypeChecker_Env.conj_guard g_f_b g_repr)
in ((uu____9068), (uu____9081))))
end)))
end)))
end))
in (match (uu____8637) with
| (k, g_k) -> begin
((

let uu____9091 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____9091) with
| true -> begin
(

let uu____9096 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print1 "tc_layered_lift: before unification k: %s\n" uu____9096))
end
| uu____9099 -> begin
()
end));
(

let g1 = (FStar_TypeChecker_Rel.teq env lift_ty k)
in ((FStar_TypeChecker_Rel.force_trivial_guard env g_k);
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let uu____9105 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____9105) with
| true -> begin
(

let uu____9110 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print1 "After unification k: %s\n" uu____9110))
end
| uu____9113 -> begin
()
end));
(

let uu____9115 = (

let uu____9128 = (FStar_TypeChecker_Util.generalize_universes env0 lift2)
in (match (uu____9128) with
| (inst_us, lift3) -> begin
((match ((Prims.op_disEquality (FStar_List.length inst_us) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____9155 = (

let uu____9161 = (

let uu____9163 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.source)
in (

let uu____9165 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.target)
in (

let uu____9167 = (

let uu____9169 = (FStar_All.pipe_right inst_us FStar_List.length)
in (FStar_All.pipe_right uu____9169 FStar_Util.string_of_int))
in (

let uu____9176 = (FStar_Syntax_Print.term_to_string lift3)
in (FStar_Util.format4 "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)" uu____9163 uu____9165 uu____9167 uu____9176)))))
in ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (uu____9161)))
in (FStar_Errors.raise_error uu____9155 r))
end
| uu____9180 -> begin
()
end);
(

let uu____9182 = ((Prims.op_Equality (FStar_List.length us1) (Prims.parse_int "0")) || ((Prims.op_Equality (FStar_List.length us1) (FStar_List.length inst_us)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____9191 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____9191 (Prims.parse_int "0")))) us1 inst_us)))
in (match (uu____9182) with
| true -> begin
(

let uu____9208 = (

let uu____9211 = (FStar_All.pipe_right k (FStar_TypeChecker_Normalize.remove_uvar_solutions env))
in (FStar_All.pipe_right uu____9211 (FStar_Syntax_Subst.close_univ_vars inst_us)))
in ((inst_us), (lift3), (uu____9208)))
end
| uu____9220 -> begin
(

let uu____9222 = (

let uu____9228 = (

let uu____9230 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.source)
in (

let uu____9232 = (FStar_Ident.string_of_lid sub1.FStar_Syntax_Syntax.target)
in (

let uu____9234 = (

let uu____9236 = (FStar_All.pipe_right us1 FStar_List.length)
in (FStar_All.pipe_right uu____9236 FStar_Util.string_of_int))
in (

let uu____9243 = (

let uu____9245 = (FStar_All.pipe_right inst_us FStar_List.length)
in (FStar_All.pipe_right uu____9245 FStar_Util.string_of_int))
in (

let uu____9252 = (FStar_Syntax_Print.term_to_string lift3)
in (FStar_Util.format5 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)" uu____9230 uu____9232 uu____9234 uu____9243 uu____9252))))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____9228)))
in (FStar_Errors.raise_error uu____9222 r))
end));
)
end))
in (match (uu____9115) with
| (us2, lift3, lift_wp) -> begin
(

let sub2 = (

let uu___987_9284 = sub1
in {FStar_Syntax_Syntax.source = uu___987_9284.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___987_9284.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (((us2), (lift_wp))); FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.Some (((us2), (lift3)))})
in ((

let uu____9294 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("LayeredEffects")))
in (match (uu____9294) with
| true -> begin
(

let uu____9299 = (FStar_Syntax_Print.sub_eff_to_string sub2)
in (FStar_Util.print1 "Final sub_effect: %s\n" uu____9299))
end
| uu____9302 -> begin
()
end));
sub2;
))
end));
));
)
end)));
));
)
end))
end));
))
end));
))


let tc_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sub_eff  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sub_eff = (fun env sub1 r -> (

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.target)
in (

let uu____9322 = ((FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) || (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered))
in (match (uu____9322) with
| true -> begin
(tc_layered_lift env sub1)
end
| uu____9327 -> begin
(

let uu____9329 = (

let uu____9336 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.source)
in (monad_signature env sub1.FStar_Syntax_Syntax.source uu____9336))
in (match (uu____9329) with
| (a, wp_a_src) -> begin
(

let uu____9343 = (

let uu____9350 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.target)
in (monad_signature env sub1.FStar_Syntax_Syntax.target uu____9350))
in (match (uu____9343) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____9358 = (

let uu____9361 = (

let uu____9362 = (

let uu____9369 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____9369)))
in FStar_Syntax_Syntax.NT (uu____9362))
in (uu____9361)::[])
in (FStar_Syntax_Subst.subst uu____9358 wp_b_tgt))
in (

let expected_k = (

let uu____9377 = (

let uu____9386 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____9393 = (

let uu____9402 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____9402)::[])
in (uu____9386)::uu____9393))
in (

let uu____9427 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____9377 uu____9427)))
in (

let repr_type = (fun eff_name a1 wp -> ((

let uu____9449 = (

let uu____9451 = (FStar_TypeChecker_Env.is_reifiable_effect env eff_name)
in (not (uu____9451)))
in (match (uu____9449) with
| true -> begin
(

let uu____9454 = (

let uu____9460 = (FStar_Util.format1 "Effect %s cannot be reified" eff_name.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____9460)))
in (

let uu____9464 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____9454 uu____9464)))
end
| uu____9465 -> begin
()
end));
(

let uu____9467 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____9467) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (

let uu____9500 = (

let uu____9501 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr)
in (FStar_All.pipe_right uu____9501 FStar_Util.must))
in (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed uu____9500))
in (

let uu____9508 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____9509 = (

let uu____9516 = (

let uu____9517 = (

let uu____9534 = (

let uu____9545 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____9554 = (

let uu____9565 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____9565)::[])
in (uu____9545)::uu____9554))
in ((repr), (uu____9534)))
in FStar_Syntax_Syntax.Tm_app (uu____9517))
in (FStar_Syntax_Syntax.mk uu____9516))
in (uu____9509 FStar_Pervasives_Native.None uu____9508))))
end));
))
in (

let uu____9610 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let uu____9783 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9794 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9794) with
| (usubst, uvs1) -> begin
(

let uu____9817 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let uu____9818 = (FStar_Syntax_Subst.subst usubst lift_wp)
in ((uu____9817), (uu____9818))))
end))
end
| uu____9819 -> begin
((env), (lift_wp))
end)
in (match (uu____9783) with
| (env1, lift_wp1) -> begin
(

let lift_wp2 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env1 lift_wp1 expected_k)
end
| uu____9865 -> begin
(

let lift_wp2 = (FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 lift_wp1 expected_k)
in (

let uu____9868 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp2)
in ((uvs), (uu____9868))))
end)
in ((lift), (lift_wp2)))
end))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let uu____9939 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9954 = (FStar_Syntax_Subst.univ_var_opening what)
in (match (uu____9954) with
| (usubst, uvs) -> begin
(

let uu____9979 = (FStar_Syntax_Subst.subst usubst lift)
in ((uvs), (uu____9979)))
end))
end
| uu____9982 -> begin
(([]), (lift))
end)
in (match (uu____9939) with
| (uvs, lift1) -> begin
((

let uu____10015 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____10015) with
| true -> begin
(

let uu____10019 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____10019))
end
| uu____10022 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant env FStar_Range.dummyRange))
in (

let uu____10025 = (

let uu____10032 = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (FStar_TypeChecker_TcTerm.tc_term uu____10032 lift1))
in (match (uu____10025) with
| (lift2, comp, uu____10057) -> begin
(

let uu____10058 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____10058) with
| (uu____10087, lift_wp, lift_elab) -> begin
(

let lift_wp1 = (FStar_TypeChecker_DMFF.recheck_debug "lift-wp" env lift_wp)
in (

let lift_elab1 = (FStar_TypeChecker_DMFF.recheck_debug "lift-elab" env lift_elab)
in (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____10119 = (

let uu____10130 = (FStar_TypeChecker_Util.generalize_universes env lift_elab1)
in FStar_Pervasives_Native.Some (uu____10130))
in (

let uu____10147 = (FStar_TypeChecker_Util.generalize_universes env lift_wp1)
in ((uu____10119), (uu____10147))))
end
| uu____10174 -> begin
(

let uu____10176 = (

let uu____10187 = (

let uu____10196 = (FStar_Syntax_Subst.close_univ_vars uvs lift_elab1)
in ((uvs), (uu____10196)))
in FStar_Pervasives_Native.Some (uu____10187))
in (

let uu____10211 = (

let uu____10220 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp1)
in ((uvs), (uu____10220)))
in ((uu____10176), (uu____10211))))
end)))
end))
end)));
)
end))
end)
in (match (uu____9610) with
| (lift, lift_wp) -> begin
(

let env1 = (

let uu___1067_10284 = env
in {FStar_TypeChecker_Env.solver = uu___1067_10284.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1067_10284.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1067_10284.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1067_10284.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1067_10284.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1067_10284.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1067_10284.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1067_10284.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1067_10284.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1067_10284.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___1067_10284.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1067_10284.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1067_10284.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1067_10284.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1067_10284.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1067_10284.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1067_10284.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1067_10284.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1067_10284.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1067_10284.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1067_10284.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1067_10284.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1067_10284.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1067_10284.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1067_10284.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1067_10284.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1067_10284.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1067_10284.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1067_10284.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1067_10284.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1067_10284.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1067_10284.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1067_10284.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1067_10284.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1067_10284.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___1067_10284.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___1067_10284.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1067_10284.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1067_10284.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1067_10284.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1067_10284.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1067_10284.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___1067_10284.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___1067_10284.FStar_TypeChecker_Env.erasable_types_tab})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let uu____10317 = (

let uu____10322 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____10322) with
| (usubst, uvs1) -> begin
(

let uu____10345 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in (

let uu____10346 = (FStar_Syntax_Subst.subst usubst lift1)
in ((uu____10345), (uu____10346))))
end))
in (match (uu____10317) with
| (env2, lift2) -> begin
(

let uu____10351 = (

let uu____10358 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____10358))
in (match (uu____10351) with
| (a1, wp_a_src1) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None wp_a_src1)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub1.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env2 (FStar_Pervasives_Native.snd lift_wp))
in (

let lift_wp_a = (

let uu____10384 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____10385 = (

let uu____10392 = (

let uu____10393 = (

let uu____10410 = (

let uu____10421 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____10430 = (

let uu____10441 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____10441)::[])
in (uu____10421)::uu____10430))
in ((lift_wp1), (uu____10410)))
in FStar_Syntax_Syntax.Tm_app (uu____10393))
in (FStar_Syntax_Syntax.mk uu____10392))
in (uu____10385 FStar_Pervasives_Native.None uu____10384)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____10489 = (

let uu____10498 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____10505 = (

let uu____10514 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____10521 = (

let uu____10530 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____10530)::[])
in (uu____10514)::uu____10521))
in (uu____10498)::uu____10505))
in (

let uu____10561 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____10489 uu____10561)))
in (

let uu____10564 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____10564) with
| (expected_k2, uu____10574, uu____10575) -> begin
(

let lift3 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env2 lift2 expected_k2)
end
| uu____10580 -> begin
(

let lift3 = (FStar_TypeChecker_TcTerm.tc_check_trivial_guard env2 lift2 expected_k2)
in (

let uu____10583 = (FStar_Syntax_Subst.close_univ_vars uvs lift3)
in ((uvs), (uu____10583))))
end)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end))
end))
end)
in ((

let uu____10591 = (

let uu____10593 = (

let uu____10595 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____10595 FStar_List.length))
in (Prims.op_disEquality uu____10593 (Prims.parse_int "1")))
in (match (uu____10591) with
| true -> begin
(

let uu____10618 = (

let uu____10624 = (

let uu____10626 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____10628 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____10630 = (

let uu____10632 = (

let uu____10634 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____10634 FStar_List.length))
in (FStar_All.pipe_right uu____10632 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____10626 uu____10628 uu____10630))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____10624)))
in (FStar_Errors.raise_error uu____10618 r))
end
| uu____10658 -> begin
()
end));
(

let uu____10661 = ((FStar_Util.is_some lift1) && (

let uu____10664 = (

let uu____10666 = (

let uu____10669 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____10669 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____10666 FStar_List.length))
in (Prims.op_disEquality uu____10664 (Prims.parse_int "1"))))
in (match (uu____10661) with
| true -> begin
(

let uu____10708 = (

let uu____10714 = (

let uu____10716 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____10718 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____10720 = (

let uu____10722 = (

let uu____10724 = (

let uu____10727 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____10727 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____10724 FStar_List.length))
in (FStar_All.pipe_right uu____10722 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____10716 uu____10718 uu____10720))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____10714)))
in (FStar_Errors.raise_error uu____10708 r))
end
| uu____10767 -> begin
()
end));
(

let uu___1104_10769 = sub1
in {FStar_Syntax_Syntax.source = uu___1104_10769.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___1104_10769.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1});
)))
end)))))
end))
end))
end)))))


let tc_effect_abbrev : FStar_TypeChecker_Env.env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)  ->  FStar_Range.range  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun env uu____10800 r -> (match (uu____10800) with
| (lid, uvs, tps, c) -> begin
(

let env0 = env
in (

let uu____10823 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((env), (uvs), (tps), (c))
end
| uu____10849 -> begin
(

let uu____10851 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____10851) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____10882 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____10882 c))
in (

let uu____10891 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in ((uu____10891), (uvs1), (tps1), (c1)))))
end))
end)
in (match (uu____10823) with
| (env1, uvs1, tps1, c1) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____10911 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____10911) with
| (tps2, c2) -> begin
(

let uu____10926 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps2)
in (match (uu____10926) with
| (tps3, env3, us) -> begin
(

let uu____10944 = (FStar_TypeChecker_TcTerm.tc_comp env3 c2)
in (match (uu____10944) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let expected_result_typ = (match (tps3) with
| ((x, uu____10970))::uu____10971 -> begin
(FStar_Syntax_Syntax.bv_to_name x)
end
| uu____10990 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), ("Effect abbreviations must bind at least the result type")) r)
end)
in (

let def_result_typ = (FStar_Syntax_Util.comp_result c3)
in (

let uu____10998 = (

let uu____11000 = (FStar_TypeChecker_Rel.teq_nosmt_force env3 expected_result_typ def_result_typ)
in (not (uu____11000)))
in (match (uu____10998) with
| true -> begin
(

let uu____11003 = (

let uu____11009 = (

let uu____11011 = (FStar_Syntax_Print.term_to_string expected_result_typ)
in (

let uu____11013 = (FStar_Syntax_Print.term_to_string def_result_typ)
in (FStar_Util.format2 "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`" uu____11011 uu____11013)))
in ((FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch), (uu____11009)))
in (FStar_Errors.raise_error uu____11003 r))
end
| uu____11017 -> begin
()
end))));
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____11021 = (

let uu____11022 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____11022))
in (match (uu____11021) with
| (uvs2, t) -> begin
(

let uu____11051 = (

let uu____11056 = (

let uu____11069 = (

let uu____11070 = (FStar_Syntax_Subst.compress t)
in uu____11070.FStar_Syntax_Syntax.n)
in ((tps4), (uu____11069)))
in (match (uu____11056) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____11085, c5)) -> begin
(([]), (c5))
end
| (uu____11127, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____11166 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____11051) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____11198 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____11198) with
| (uu____11203, t1) -> begin
(

let uu____11205 = (

let uu____11211 = (

let uu____11213 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____11215 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____11219 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____11213 uu____11215 uu____11219))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____11211)))
in (FStar_Errors.raise_error uu____11205 r))
end))
end
| uu____11223 -> begin
()
end);
((lid), (uvs2), (tps5), (c5));
)
end))
end))));
)
end))
end))
end)))
end)))
end))




