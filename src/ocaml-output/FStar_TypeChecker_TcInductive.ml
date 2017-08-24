
open Prims
open FStar_Pervasives

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data) -> begin
(

let uu____30 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____30) with
| (tps1, k1) -> begin
(

let uu____39 = (FStar_TypeChecker_TcTerm.tc_binders env tps1)
in (match (uu____39) with
| (tps2, env_tps, guard_params, us) -> begin
(

let k2 = (FStar_TypeChecker_Normalize.unfold_whnf env k1)
in (

let uu____53 = (FStar_Syntax_Util.arrow_formals k2)
in (match (uu____53) with
| (indices, t) -> begin
(

let uu____77 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____77) with
| (indices1, env', guard_indices, us') -> begin
(

let uu____90 = (

let uu____93 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____93) with
| (t1, uu____100, g) -> begin
(

let uu____102 = (

let uu____103 = (

let uu____104 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____104))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____103))
in ((t1), (uu____102)))
end))
in (match (uu____90) with
| (t1, guard) -> begin
(

let k3 = (

let uu____114 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow indices1 uu____114))
in (

let uu____117 = (FStar_Syntax_Util.type_u ())
in (match (uu____117) with
| (t_type, u) -> begin
((

let uu____127 = (FStar_TypeChecker_Rel.teq env' t1 t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____127));
(

let t_tc = (

let uu____131 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow (FStar_List.append tps2 indices1) uu____131))
in (

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let k4 = (FStar_Syntax_Subst.close tps3 k3)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____139 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____139), ((

let uu___84_143 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps3), (k4), (mutuals), (data))); FStar_Syntax_Syntax.sigrng = uu___84_143.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___84_143.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___84_143.FStar_Syntax_Syntax.sigmeta})), (u), (guard)))))));
)
end)))
end))
end))
end)))
end))
end))
end
| uu____147 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, _mutual_tcs) -> begin
(

let uu____184 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____198 -> (match (uu____198) with
| (se1, u_tc) -> begin
(

let uu____207 = (

let uu____208 = (

let uu____209 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____209))
in (FStar_Ident.lid_equals tc_lid uu____208))
in (match (uu____207) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____219, uu____220, tps, uu____222, uu____223, uu____224) -> begin
(

let tps1 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____243 -> (match (uu____243) with
| (x, uu____250) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____253 = (

let uu____257 = (FStar_TypeChecker_Env.push_binders env tps2)
in ((uu____257), (tps2), (u_tc)))
in FStar_Pervasives_Native.Some (uu____253))))
end
| uu____261 -> begin
(failwith "Impossible")
end)
end
| uu____266 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (tps_u_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(match ((FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid)) with
| true -> begin
((env), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____291 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____184) with
| (env1, tps, u_tc) -> begin
(

let uu____300 = (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t)
in (

let uu____309 = (

let uu____310 = (FStar_Syntax_Subst.compress t1)
in uu____310.FStar_Syntax_Syntax.n)
in (match (uu____309) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____332 = (FStar_Util.first_N ntps bs)
in (match (uu____332) with
| (uu____350, bs') -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____382 -> (match (uu____382) with
| (x, uu____386) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____387 = (FStar_Syntax_Subst.subst subst1 t2)
in (FStar_Syntax_Util.arrow_formals uu____387))))
end))
end
| uu____388 -> begin
(([]), (t1))
end)))
in (match (uu____300) with
| (arguments, result) -> begin
((

let uu____409 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____409) with
| true -> begin
(

let uu____410 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____411 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____412 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____410 uu____411 uu____412))))
end
| uu____413 -> begin
()
end));
(

let uu____414 = (FStar_TypeChecker_TcTerm.tc_tparams env1 arguments)
in (match (uu____414) with
| (arguments1, env', us) -> begin
(

let uu____423 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____423) with
| (result1, res_lcomp) -> begin
((

let uu____431 = (

let uu____432 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____432.FStar_Syntax_Syntax.n)
in (match (uu____431) with
| FStar_Syntax_Syntax.Tm_type (uu____435) -> begin
()
end
| ty -> begin
(

let uu____437 = (

let uu____438 = (

let uu____441 = (

let uu____442 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____443 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____442 uu____443)))
in ((uu____441), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____438))
in (FStar_Pervasives.raise uu____437))
end));
(

let uu____444 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____444) with
| (head1, uu____457) -> begin
((

let uu____473 = (

let uu____474 = (FStar_Syntax_Subst.compress head1)
in uu____474.FStar_Syntax_Syntax.n)
in (match (uu____473) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____478 -> begin
(

let uu____479 = (

let uu____480 = (

let uu____483 = (

let uu____484 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____485 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____484 uu____485)))
in ((uu____483), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____480))
in (FStar_Pervasives.raise uu____479))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____490 u_x -> (match (uu____490) with
| (x, uu____495) -> begin
(

let uu____496 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____496))
end)) FStar_TypeChecker_Rel.trivial_guard arguments1 us)
in (

let t1 = (

let uu____500 = (

let uu____504 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____518 -> (match (uu____518) with
| (x, uu____525) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____504 arguments1))
in (

let uu____530 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____500 uu____530)))
in (((

let uu___85_533 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t1), (tc_lid), (ntps), ([]))); FStar_Syntax_Syntax.sigrng = uu___85_533.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___85_533.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___85_533.FStar_Syntax_Syntax.sigmeta})), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____538 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map FStar_Pervasives_Native.snd tcs)
in (

let g1 = (

let uu___86_574 = g
in {FStar_TypeChecker_Env.guard_f = uu___86_574.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___86_574.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((FStar_Pervasives_Native.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___86_574.FStar_TypeChecker_Env.implicits})
in ((

let uu____580 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____580) with
| true -> begin
(

let uu____581 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____581))
end
| uu____582 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____592 -> (match (uu____592) with
| (se, uu____596) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____597, uu____598, tps, k, uu____601, uu____602) -> begin
(

let uu____607 = (

let uu____608 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____608))
in (FStar_Syntax_Syntax.null_binder uu____607))
end
| uu____615 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____621, uu____622, t, uu____624, uu____625, uu____626) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____629 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____633 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____633))
in ((

let uu____637 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____637) with
| true -> begin
(

let uu____638 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____638))
end
| uu____639 -> begin
()
end));
(

let uu____640 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____640) with
| (uvs, t1) -> begin
((

let uu____650 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____650) with
| true -> begin
(

let uu____651 = (

let uu____652 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____652 (FStar_String.concat ", ")))
in (

let uu____658 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____651 uu____658)))
end
| uu____659 -> begin
()
end));
(

let uu____660 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____660) with
| (uvs1, t2) -> begin
(

let uu____669 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____669) with
| (args, uu____682) -> begin
(

let uu____693 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____693) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____730 uu____731 -> (match (((uu____730), (uu____731))) with
| ((x, uu____741), (se, uu____743)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____749, tps, uu____751, mutuals, datas1) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____759 = (

let uu____767 = (

let uu____768 = (FStar_Syntax_Subst.compress ty)
in uu____768.FStar_Syntax_Syntax.n)
in (match (uu____767) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____790 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____790) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____833 -> begin
(

let uu____837 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) uu____837 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps1), (t3)))
end))
end
| uu____856 -> begin
(([]), (ty))
end))
in (match (uu____759) with
| (tps1, t3) -> begin
(

let uu___87_874 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1))); FStar_Syntax_Syntax.sigrng = uu___87_874.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___87_874.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___87_874.FStar_Syntax_Syntax.sigmeta})
end)))
end
| uu____882 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____886 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_29 -> FStar_Syntax_Syntax.U_name (_0_29))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___80_903 -> (match (uu___80_903) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____908, uu____909, uu____910, uu____911, uu____912); FStar_Syntax_Syntax.sigrng = uu____913; FStar_Syntax_Syntax.sigquals = uu____914; FStar_Syntax_Syntax.sigmeta = uu____915} -> begin
((tc), (uvs_universes))
end
| uu____922 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____928 d -> (match (uu____928) with
| (t3, uu____933) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____935, uu____936, tc, ntps, mutuals) -> begin
(

let ty = (

let uu____943 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____943 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___88_944 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___88_944.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___88_944.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___88_944.FStar_Syntax_Syntax.sigmeta}))
end
| uu____946 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs1), (datas1))))
end))
end))
end));
)
end));
))));
))))


let debug_log : FStar_TypeChecker_Env.env_t  ->  Prims.string  ->  Prims.unit = (fun env s -> (

let uu____955 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____955) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____956 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____963 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____963)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____972 = (

let uu____973 = (FStar_Syntax_Subst.compress t)
in uu____973.FStar_Syntax_Syntax.n)
in (match (uu____972) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____989 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____992 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1011 = (FStar_ST.read unfolded)
in (FStar_List.existsML (fun uu____1023 -> (match (uu____1023) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1043 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (FStar_Pervasives_Native.fst uu____1043))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst a')))) true args l)))
end)) uu____1011)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____1138 = (

let uu____1139 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____1139))
in (debug_log env uu____1138));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1142 = (

let uu____1143 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1143))
in (debug_log env uu____1142));
((

let uu____1144 = (ty_occurs_in ty_lid btype1)
in (not (uu____1144))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1146 = (

let uu____1147 = (FStar_Syntax_Subst.compress btype1)
in uu____1147.FStar_Syntax_Syntax.n)
in (match (uu____1146) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1166 = (try_get_fv t)
in (match (uu____1166) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1178 -> (match (uu____1178) with
| (t1, uu____1182) -> begin
(

let uu____1183 = (ty_occurs_in ty_lid t1)
in (not (uu____1183)))
end)) args);
)
end
| uu____1184 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1203 = (

let uu____1204 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____1204)))
in (match (uu____1203) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____1206 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____1210 -> (match (uu____1210) with
| (b, uu____1214) -> begin
(

let uu____1215 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____1215)))
end)) sbs) && (

let uu____1216 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____1216) with
| (uu____1219, return_type) -> begin
(

let uu____1221 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____1221))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1222) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____1224) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1227) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1234) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____1240, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____1275 -> (match (uu____1275) with
| (p, uu____1283, t) -> begin
(

let bs = (

let uu____1293 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____1293))
in (

let uu____1295 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1295) with
| (bs1, t1) -> begin
(

let uu____1300 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____1300))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1302, uu____1303) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1333 -> begin
((

let uu____1335 = (

let uu____1336 = (

let uu____1337 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____1338 = (

let uu____1339 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____1339))
in (Prims.strcat uu____1337 uu____1338)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____1336))
in (debug_log env uu____1335));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1347 = (

let uu____1348 = (

let uu____1349 = (

let uu____1350 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1350))
in (Prims.strcat ilid.FStar_Ident.str uu____1349))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1348))
in (debug_log env uu____1347));
(

let uu____1351 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1351) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1360 -> begin
(

let uu____1361 = (already_unfolded ilid args unfolded env)
in (match (uu____1361) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1363 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1366 = (

let uu____1367 = (

let uu____1368 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1368 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1367))
in (debug_log env uu____1366));
(

let uu____1370 = (

let uu____1371 = (FStar_ST.read unfolded)
in (

let uu____1375 = (

let uu____1379 = (

let uu____1387 = (

let uu____1393 = (FStar_List.splitAt num_ibs args)
in (FStar_Pervasives_Native.fst uu____1393))
in ((ilid), (uu____1387)))
in (uu____1379)::[])
in (FStar_List.append uu____1371 uu____1375)))
in (FStar_ST.write unfolded uu____1370));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1451 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1451) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (FStar_Pervasives_Native.Some (u)))
end
| uu____1463 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1466 = (

let uu____1467 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1467))
in (debug_log env uu____1466));
(

let uu____1468 = (

let uu____1469 = (FStar_Syntax_Subst.compress dt1)
in uu____1469.FStar_Syntax_Syntax.n)
in (match (uu____1468) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1485 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1485) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____1512 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____1512 dbs1))
in (

let c1 = (

let uu____1515 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____1515 c))
in (

let uu____1517 = (FStar_List.splitAt num_ibs args)
in (match (uu____1517) with
| (args1, uu____1535) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst ib)), ((FStar_Pervasives_Native.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____1581 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____1581 c1))
in ((

let uu____1589 = (

let uu____1590 = (

let uu____1591 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____1592 = (

let uu____1593 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____1593))
in (Prims.strcat uu____1591 uu____1592)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1590))
in (debug_log env uu____1589));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1594 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1596 = (

let uu____1597 = (FStar_Syntax_Subst.compress dt1)
in uu____1597.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1596 ilid num_ibs unfolded env));
)
end));
));
)
end));
))
and ty_nested_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term'  ->  FStar_Ident.lident  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid t ilid num_ibs unfolded env -> (match (t) with
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((debug_log env "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
(

let uu____1623 = (try_get_fv t1)
in (match (uu____1623) with
| (fv, uu____1627) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1632 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1646 = (

let uu____1647 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1647))
in (debug_log env uu____1646));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____1649 = (FStar_List.fold_left (fun uu____1656 b -> (match (uu____1656) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1668 -> begin
(

let uu____1669 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1670 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1669), (uu____1670))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____1649) with
| (b, uu____1676) -> begin
b
end)));
)
end
| uu____1677 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1696 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1696) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (FStar_Pervasives_Native.Some (u)))
end
| uu____1708 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1710 = (

let uu____1711 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1711))
in (debug_log env uu____1710));
(

let uu____1712 = (

let uu____1713 = (FStar_Syntax_Subst.compress dt)
in uu____1713.FStar_Syntax_Syntax.n)
in (match (uu____1712) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1716) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1719) -> begin
(

let dbs1 = (

let uu____1734 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (FStar_Pervasives_Native.snd uu____1734))
in (

let dbs2 = (

let uu____1756 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1756 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____1760 = (

let uu____1761 = (

let uu____1762 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____1762 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1761))
in (debug_log env uu____1760));
(

let uu____1768 = (FStar_List.fold_left (fun uu____1775 b -> (match (uu____1775) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1787 -> begin
(

let uu____1788 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1789 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1788), (uu____1789))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____1768) with
| (b, uu____1795) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1796, uu____1797) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1813 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1831 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1841, uu____1842, uu____1843) -> begin
((lid), (us), (bs))
end
| uu____1848 -> begin
(failwith "Impossible!")
end)
in (match (uu____1831) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1855 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1855) with
| (ty_usubst, ty_us1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env ty_us1)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ty_bs)
in (

let ty_bs1 = (FStar_Syntax_Subst.subst_binders ty_usubst ty_bs)
in (

let ty_bs2 = (FStar_Syntax_Subst.open_binders ty_bs1)
in (

let uu____1870 = (

let uu____1872 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (FStar_Pervasives_Native.snd uu____1872))
in (FStar_List.for_all (fun d -> (

let uu____1878 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____1878 unfolded_inductives env2))) uu____1870))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1885, uu____1886, t, uu____1888, uu____1889, uu____1890) -> begin
t
end
| uu____1893 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1910 = (

let uu____1911 = (FStar_Syntax_Subst.compress dt1)
in uu____1911.FStar_Syntax_Syntax.n)
in (match (uu____1910) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1915) -> begin
(

let dbs1 = (

let uu____1930 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____1930))
in (

let dbs2 = (

let uu____1952 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1952 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____1961 = (

let uu____1962 = (

let uu____1963 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____1963)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____1962))
in (uu____1961 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sort_range = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____1970 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____1970 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____1975 = (

let uu____1976 = (

let uu____1977 = (

let uu____1978 = (

let uu____1979 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____1979 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____1978))
in (uu____1977)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____1976))
in (uu____1975 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____1996 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2055 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2067, bs, t, uu____2070, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2077 -> begin
(failwith "Impossible!")
end)
in (match (uu____2055) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2102 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2102 t))
in (

let uu____2109 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2109) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2129 = (

let uu____2130 = (FStar_Syntax_Subst.compress t2)
in uu____2130.FStar_Syntax_Syntax.n)
in (match (uu____2129) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2137) -> begin
ibs
end
| uu____2148 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2153 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____2154 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2153 uu____2154)))
in (

let ind1 = (

let uu____2159 = (

let uu____2160 = (FStar_List.map (fun uu____2165 -> (match (uu____2165) with
| (bv, aq) -> begin
(

let uu____2172 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2172), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2160))
in (uu____2159 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2180 = (

let uu____2181 = (FStar_List.map (fun uu____2186 -> (match (uu____2186) with
| (bv, aq) -> begin
(

let uu____2193 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2193), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2181))
in (uu____2180 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2201 = (

let uu____2202 = (

let uu____2203 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2203)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2202))
in (uu____2201 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____2217 = acc
in (match (uu____2217) with
| (uu____2225, en, uu____2227, uu____2228) -> begin
(

let opt = (

let uu____2237 = (

let uu____2238 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____2238))
in (FStar_TypeChecker_Rel.try_subtype' en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____2237 false))
in (match (opt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____2241) -> begin
true
end))
end))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____2245 = (

let uu____2246 = (

let uu____2247 = (

let uu____2248 = (

let uu____2249 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____2249))
in (uu____2248)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2247))
in (uu____2246 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____2245))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___89_2258 = fml
in (

let uu____2259 = (

let uu____2260 = (

let uu____2265 = (

let uu____2266 = (

let uu____2273 = (

let uu____2275 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2275)::[])
in (uu____2273)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2266))
in ((fml), (uu____2265)))
in FStar_Syntax_Syntax.Tm_meta (uu____2260))
in {FStar_Syntax_Syntax.n = uu____2259; FStar_Syntax_Syntax.tk = uu___89_2258.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___89_2258.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___89_2258.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____2287 = (

let uu____2288 = (

let uu____2289 = (

let uu____2290 = (

let uu____2291 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____2291 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____2290))
in (uu____2289)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2288))
in (uu____2287 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____2313 = (

let uu____2314 = (

let uu____2315 = (

let uu____2316 = (

let uu____2317 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____2317 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____2316))
in (uu____2315)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2314))
in (uu____2313 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml3)
in (

let uu____2337 = acc
in (match (uu____2337) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs2)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs1)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2371, uu____2372, uu____2373, t_lid, uu____2375, uu____2376) -> begin
(t_lid = lid)
end
| uu____2379 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____2383 = (optimized_haseq_soundness_for_data lid d usubst bs2)
in (FStar_Syntax_Util.mk_conj acc1 uu____2383))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2385 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2388 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml3)))::[]))), (env2), (uu____2385), (uu____2388)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2454, us, uu____2456, uu____2457, uu____2458, uu____2459) -> begin
us
end
| uu____2464 -> begin
(failwith "Impossible!")
end))
in (

let uu____2465 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2465) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____2481 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2481) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2513 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____2513) with
| (phi1, uu____2518) -> begin
((

let uu____2520 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____2520) with
| true -> begin
(

let uu____2521 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____2521))
end
| uu____2522 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2529 -> (match (uu____2529) with
| (lid, fml) -> begin
(

let se = (tc_assume env2 lid fml [] FStar_Range.dummyRange)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
ses;
));
)
end)))
end)));
))
end))))


let unoptimized_haseq_data : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun usubst bs haseq_ind mutuals acc data -> (

let rec is_mutual = (fun t -> (

let uu____2572 = (

let uu____2573 = (FStar_Syntax_Subst.compress t)
in uu____2573.FStar_Syntax_Syntax.n)
in (match (uu____2572) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2583) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2610 = (is_mutual t')
in (match (uu____2610) with
| true -> begin
true
end
| uu____2611 -> begin
(

let uu____2612 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (exists_mutual uu____2612))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2625) -> begin
(is_mutual t')
end
| uu____2630 -> begin
false
end)))
and exists_mutual = (fun uu___81_2631 -> (match (uu___81_2631) with
| [] -> begin
false
end
| (hd1)::tl1 -> begin
((is_mutual hd1) || (exists_mutual tl1))
end))
in (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____2648 = (

let uu____2649 = (FStar_Syntax_Subst.compress dt1)
in uu____2649.FStar_Syntax_Syntax.n)
in (match (uu____2648) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2655) -> begin
(

let dbs1 = (

let uu____2670 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____2670))
in (

let dbs2 = (

let uu____2692 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2692 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2704 = (

let uu____2705 = (

let uu____2706 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____2706)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2705))
in (uu____2704 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____2712 = (is_mutual sort)
in (match (uu____2712) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2713 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____2719 = (

let uu____2720 = (

let uu____2721 = (

let uu____2722 = (

let uu____2723 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____2723 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____2722))
in (uu____2721)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2720))
in (uu____2719 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____2740 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2783 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2795, bs, t, uu____2798, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2805 -> begin
(failwith "Impossible!")
end)
in (match (uu____2783) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2821 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2821 t))
in (

let uu____2828 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2828) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2839 = (

let uu____2840 = (FStar_Syntax_Subst.compress t2)
in uu____2840.FStar_Syntax_Syntax.n)
in (match (uu____2839) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2847) -> begin
ibs
end
| uu____2858 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2863 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____2864 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2863 uu____2864)))
in (

let ind1 = (

let uu____2869 = (

let uu____2870 = (FStar_List.map (fun uu____2875 -> (match (uu____2875) with
| (bv, aq) -> begin
(

let uu____2882 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2882), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2870))
in (uu____2869 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2890 = (

let uu____2891 = (FStar_List.map (fun uu____2896 -> (match (uu____2896) with
| (bv, aq) -> begin
(

let uu____2903 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2903), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2891))
in (uu____2890 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2911 = (

let uu____2912 = (

let uu____2913 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2913)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2912))
in (uu____2911 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2921, uu____2922, uu____2923, t_lid, uu____2925, uu____2926) -> begin
(t_lid = lid)
end
| uu____2929 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___90_2935 = fml
in (

let uu____2936 = (

let uu____2937 = (

let uu____2942 = (

let uu____2943 = (

let uu____2950 = (

let uu____2952 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2952)::[])
in (uu____2950)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2943))
in ((fml), (uu____2942)))
in FStar_Syntax_Syntax.Tm_meta (uu____2937))
in {FStar_Syntax_Syntax.n = uu____2936; FStar_Syntax_Syntax.tk = uu___90_2935.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___90_2935.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___90_2935.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____2964 = (

let uu____2965 = (

let uu____2966 = (

let uu____2967 = (

let uu____2968 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____2968 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____2967))
in (uu____2966)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2965))
in (uu____2964 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____2990 = (

let uu____2991 = (

let uu____2992 = (

let uu____2993 = (

let uu____2994 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____2994 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____2993))
in (uu____2992)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2991))
in (uu____2990 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3063, uu____3064, uu____3065, uu____3066, uu____3067) -> begin
lid
end
| uu____3072 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3073 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3081, uu____3082, uu____3083, uu____3084) -> begin
((lid), (us))
end
| uu____3089 -> begin
(failwith "Impossible!")
end))
in (match (uu____3073) with
| (lid, us) -> begin
(

let uu____3095 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3095) with
| (usubst, us1) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us1) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let se = (

let uu____3113 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env1 uu____3113 fml [] FStar_Range.dummyRange))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3143 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___82_3153 -> (match (uu___82_3153) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____3154); FStar_Syntax_Syntax.sigrng = uu____3155; FStar_Syntax_Syntax.sigquals = uu____3156; FStar_Syntax_Syntax.sigmeta = uu____3157} -> begin
true
end
| uu____3167 -> begin
false
end))))
in (match (uu____3143) with
| (tys, datas) -> begin
((

let uu____3180 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___83_3182 -> (match (uu___83_3182) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____3183); FStar_Syntax_Syntax.sigrng = uu____3184; FStar_Syntax_Syntax.sigquals = uu____3185; FStar_Syntax_Syntax.sigmeta = uu____3186} -> begin
false
end
| uu____3195 -> begin
true
end))))
in (match (uu____3180) with
| true -> begin
(

let uu____3196 = (

let uu____3197 = (

let uu____3200 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3200)))
in FStar_Errors.Error (uu____3197))
in (FStar_Pervasives.raise uu____3196))
end
| uu____3201 -> begin
()
end));
(

let env0 = env
in (

let uu____3203 = (FStar_List.fold_right (fun tc uu____3217 -> (match (uu____3217) with
| (env1, all_tcs, g) -> begin
(

let uu____3239 = (tc_tycon env1 tc)
in (match (uu____3239) with
| (env2, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3256 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____3256) with
| true -> begin
(

let uu____3257 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3257))
end
| uu____3258 -> begin
()
end));
(

let uu____3259 = (

let uu____3260 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3260))
in ((env2), ((((tc1), (tc_u)))::all_tcs), (uu____3259)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3203) with
| (env1, tcs, g) -> begin
(

let uu____3285 = (FStar_List.fold_right (fun se uu____3293 -> (match (uu____3293) with
| (datas1, g1) -> begin
(

let uu____3304 = (

let uu____3307 = (tc_data env1 tcs)
in (uu____3307 se))
in (match (uu____3304) with
| (data, g') -> begin
(

let uu____3317 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas1), (uu____3317)))
end))
end)) datas (([]), (g)))
in (match (uu____3285) with
| (datas1, g1) -> begin
(

let uu____3329 = (generalize_and_inst_within env0 g1 tcs datas1)
in (match (uu____3329) with
| (tcs1, datas2) -> begin
(

let sig_bndle = (

let uu____3346 = (FStar_TypeChecker_Env.get_range env0)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas2)), (lids))); FStar_Syntax_Syntax.sigrng = uu____3346; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta})
in ((sig_bndle), (tcs1), (datas2)))
end))
end))
end)));
)
end)))




