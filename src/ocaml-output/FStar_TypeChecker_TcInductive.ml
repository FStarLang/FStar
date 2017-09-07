
open Prims
open FStar_Pervasives

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data) -> begin
(

let uu____42 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____42) with
| (tps1, k1) -> begin
(

let uu____57 = (FStar_TypeChecker_TcTerm.tc_binders env tps1)
in (match (uu____57) with
| (tps2, env_tps, guard_params, us) -> begin
(

let k2 = (FStar_TypeChecker_Normalize.unfold_whnf env k1)
in (

let uu____79 = (FStar_Syntax_Util.arrow_formals k2)
in (match (uu____79) with
| (indices, t) -> begin
(

let uu____118 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____118) with
| (indices1, env', guard_indices, us') -> begin
(

let uu____139 = (

let uu____144 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____144) with
| (t1, uu____156, g) -> begin
(

let uu____158 = (

let uu____159 = (

let uu____160 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____160))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____159))
in ((t1), (uu____158)))
end))
in (match (uu____139) with
| (t1, guard) -> begin
(

let k3 = (

let uu____174 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow indices1 uu____174))
in (

let uu____177 = (FStar_Syntax_Util.type_u ())
in (match (uu____177) with
| (t_type, u) -> begin
((

let uu____193 = (FStar_TypeChecker_Rel.teq env' t1 t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____193));
(

let t_tc = (

let uu____197 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow (FStar_List.append tps2 indices1) uu____197))
in (

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let k4 = (FStar_Syntax_Subst.close tps3 k3)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____207 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____207), ((

let uu___90_213 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps3), (k4), (mutuals), (data))); FStar_Syntax_Syntax.sigrng = uu___90_213.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___90_213.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___90_213.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___90_213.FStar_Syntax_Syntax.sigattrs})), (u), (guard)))))));
)
end)))
end))
end))
end)))
end))
end))
end
| uu____220 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, _mutual_tcs) -> begin
(

let uu____279 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____318 -> (match (uu____318) with
| (se1, u_tc) -> begin
(

let uu____333 = (

let uu____334 = (

let uu____335 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____335))
in (FStar_Ident.lid_equals tc_lid uu____334))
in (match (uu____333) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____354, uu____355, tps, uu____357, uu____358, uu____359) -> begin
(

let tps1 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____398 -> (match (uu____398) with
| (x, uu____410) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____414 = (

let uu____421 = (FStar_TypeChecker_Env.push_binders env tps2)
in ((uu____421), (tps2), (u_tc)))
in FStar_Pervasives_Native.Some (uu____414))))
end
| uu____428 -> begin
(failwith "Impossible")
end)
end
| uu____437 -> begin
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
| uu____485 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____279) with
| (env1, tps, u_tc) -> begin
(

let uu____499 = (

let t1 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t)
in (

let uu____513 = (

let uu____514 = (FStar_Syntax_Subst.compress t1)
in uu____514.FStar_Syntax_Syntax.n)
in (match (uu____513) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____547 = (FStar_Util.first_N ntps bs)
in (match (uu____547) with
| (uu____580, bs') -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____631 -> (match (uu____631) with
| (x, uu____637) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____638 = (FStar_Syntax_Subst.subst subst1 t2)
in (FStar_Syntax_Util.arrow_formals uu____638))))
end))
end
| uu____639 -> begin
(([]), (t1))
end)))
in (match (uu____499) with
| (arguments, result) -> begin
((

let uu____673 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____673) with
| true -> begin
(

let uu____674 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____675 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____676 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____674 uu____675 uu____676))))
end
| uu____677 -> begin
()
end));
(

let uu____678 = (FStar_TypeChecker_TcTerm.tc_tparams env1 arguments)
in (match (uu____678) with
| (arguments1, env', us) -> begin
(

let uu____692 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____692) with
| (result1, res_lcomp) -> begin
((

let uu____704 = (

let uu____705 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____705.FStar_Syntax_Syntax.n)
in (match (uu____704) with
| FStar_Syntax_Syntax.Tm_type (uu____708) -> begin
()
end
| ty -> begin
(

let uu____710 = (

let uu____711 = (

let uu____716 = (

let uu____717 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____718 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____717 uu____718)))
in ((uu____716), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____711))
in (FStar_Exn.raise uu____710))
end));
(

let uu____719 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____719) with
| (head1, uu____739) -> begin
((

let uu____761 = (

let uu____762 = (FStar_Syntax_Subst.compress head1)
in uu____762.FStar_Syntax_Syntax.n)
in (match (uu____761) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____766 -> begin
(

let uu____767 = (

let uu____768 = (

let uu____773 = (

let uu____774 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____775 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____774 uu____775)))
in ((uu____773), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____768))
in (FStar_Exn.raise uu____767))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____788 u_x -> (match (uu____788) with
| (x, uu____795) -> begin
(

let uu____796 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____796))
end)) FStar_TypeChecker_Rel.trivial_guard arguments1 us)
in (

let t1 = (

let uu____800 = (

let uu____807 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____837 -> (match (uu____837) with
| (x, uu____849) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____807 arguments1))
in (

let uu____858 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____800 uu____858)))
in (((

let uu___91_862 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t1), (tc_lid), (ntps), ([]))); FStar_Syntax_Syntax.sigrng = uu___91_862.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___91_862.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___91_862.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___91_862.FStar_Syntax_Syntax.sigattrs})), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____869 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map FStar_Pervasives_Native.snd tcs)
in (

let g1 = (

let uu___92_930 = g
in {FStar_TypeChecker_Env.guard_f = uu___92_930.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___92_930.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((FStar_Pervasives_Native.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___92_930.FStar_TypeChecker_Env.implicits})
in ((

let uu____940 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____940) with
| true -> begin
(

let uu____941 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____941))
end
| uu____942 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____969 -> (match (uu____969) with
| (se, uu____975) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____976, uu____977, tps, k, uu____980, uu____981) -> begin
(

let uu____990 = (

let uu____991 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____991))
in (FStar_Syntax_Syntax.null_binder uu____990))
end
| uu____998 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1014, uu____1015, t, uu____1017, uu____1018, uu____1019) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____1024 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____1028 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____1028))
in ((

let uu____1032 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1032) with
| true -> begin
(

let uu____1033 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____1033))
end
| uu____1034 -> begin
()
end));
(

let uu____1035 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____1035) with
| (uvs, t1) -> begin
((

let uu____1051 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1051) with
| true -> begin
(

let uu____1052 = (

let uu____1053 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____1053 (FStar_String.concat ", ")))
in (

let uu____1064 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____1052 uu____1064)))
end
| uu____1065 -> begin
()
end));
(

let uu____1066 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____1066) with
| (uvs1, t2) -> begin
(

let uu____1081 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____1081) with
| (args, uu____1103) -> begin
(

let uu____1120 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____1120) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____1203 uu____1204 -> (match (((uu____1203), (uu____1204))) with
| ((x, uu____1222), (se, uu____1224)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1234, tps, uu____1236, mutuals, datas1) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____1248 = (

let uu____1261 = (

let uu____1262 = (FStar_Syntax_Subst.compress ty)
in uu____1262.FStar_Syntax_Syntax.n)
in (match (uu____1261) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____1295 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____1295) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1367 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos)
end)
in ((tps1), (t3)))
end))
end
| uu____1390 -> begin
(([]), (ty))
end))
in (match (uu____1248) with
| (tps1, t3) -> begin
(

let uu___93_1419 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1))); FStar_Syntax_Syntax.sigrng = uu___93_1419.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___93_1419.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___93_1419.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___93_1419.FStar_Syntax_Syntax.sigattrs})
end)))
end
| uu____1432 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____1438 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_41 -> FStar_Syntax_Syntax.U_name (_0_41))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___86_1480 -> (match (uu___86_1480) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1488, uu____1489, uu____1490, uu____1491, uu____1492); FStar_Syntax_Syntax.sigrng = uu____1493; FStar_Syntax_Syntax.sigquals = uu____1494; FStar_Syntax_Syntax.sigmeta = uu____1495; FStar_Syntax_Syntax.sigattrs = uu____1496} -> begin
((tc), (uvs_universes))
end
| uu____1511 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____1534 d -> (match (uu____1534) with
| (t3, uu____1541) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____1543, uu____1544, tc, ntps, mutuals) -> begin
(

let ty = (

let uu____1553 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____1553 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___94_1554 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___94_1554.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___94_1554.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___94_1554.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___94_1554.FStar_Syntax_Syntax.sigattrs}))
end
| uu____1557 -> begin
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

let uu____1570 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____1570) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____1571 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____1580 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____1580)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____1595 = (

let uu____1596 = (FStar_Syntax_Subst.compress t)
in uu____1596.FStar_Syntax_Syntax.n)
in (match (uu____1595) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____1617 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____1622 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1663 = (FStar_ST.op_Bang unfolded)
in (FStar_List.existsML (fun uu____1711 -> (match (uu____1711) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1746 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (FStar_Pervasives_Native.fst uu____1746))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst a')))) true args l)))
end)) uu____1663)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____1898 = (

let uu____1899 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____1899))
in (debug_log env uu____1898));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1902 = (

let uu____1903 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1903))
in (debug_log env uu____1902));
((

let uu____1906 = (ty_occurs_in ty_lid btype1)
in (not (uu____1906))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1916 = (

let uu____1917 = (FStar_Syntax_Subst.compress btype1)
in uu____1917.FStar_Syntax_Syntax.n)
in (match (uu____1916) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1942 = (try_get_fv t)
in (match (uu____1942) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1958 -> (match (uu____1958) with
| (t1, uu____1964) -> begin
(

let uu____1965 = (ty_occurs_in ty_lid t1)
in (not (uu____1965)))
end)) args);
)
end
| uu____1966 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1999 = (

let uu____2000 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____2000)))
in (match (uu____1999) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____2002 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____2012 -> (match (uu____2012) with
| (b, uu____2018) -> begin
(

let uu____2019 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____2019)))
end)) sbs) && (

let uu____2024 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____2024) with
| (uu____2029, return_type) -> begin
(

let uu____2031 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____2031))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2044) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____2046) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2049) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____2068) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____2086, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____2144 -> (match (uu____2144) with
| (p, uu____2156, t) -> begin
(

let bs = (

let uu____2169 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____2169))
in (

let uu____2172 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2172) with
| (bs1, t1) -> begin
(

let uu____2179 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____2179))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____2193, uu____2194) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____2248 -> begin
((

let uu____2250 = (

let uu____2251 = (

let uu____2252 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____2253 = (

let uu____2254 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____2254))
in (Prims.strcat uu____2252 uu____2253)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____2251))
in (debug_log env uu____2250));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____2268 = (

let uu____2269 = (

let uu____2270 = (

let uu____2271 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____2271))
in (Prims.strcat ilid.FStar_Ident.str uu____2270))
in (Prims.strcat "Checking nested positivity in the inductive " uu____2269))
in (debug_log env uu____2268));
(

let uu____2272 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____2272) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____2286 -> begin
(

let uu____2287 = (already_unfolded ilid args unfolded env)
in (match (uu____2287) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____2301 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____2304 = (

let uu____2305 = (

let uu____2306 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____2306 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____2305))
in (debug_log env uu____2304));
(

let uu____2308 = (

let uu____2309 = (FStar_ST.op_Bang unfolded)
in (

let uu____2338 = (

let uu____2345 = (

let uu____2358 = (

let uu____2367 = (FStar_List.splitAt num_ibs args)
in (FStar_Pervasives_Native.fst uu____2367))
in ((ilid), (uu____2358)))
in (uu____2345)::[])
in (FStar_List.append uu____2309 uu____2338)))
in (FStar_ST.op_Colon_Equals unfolded uu____2308));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____2497 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____2497) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____2519 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____2522 = (

let uu____2523 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____2523))
in (debug_log env uu____2522));
(

let uu____2524 = (

let uu____2525 = (FStar_Syntax_Subst.compress dt1)
in uu____2525.FStar_Syntax_Syntax.n)
in (match (uu____2524) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____2547 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____2547) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____2596 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____2596 dbs1))
in (

let c1 = (

let uu____2600 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____2600 c))
in (

let uu____2603 = (FStar_List.splitAt num_ibs args)
in (match (uu____2603) with
| (args1, uu____2631) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst ib)), ((FStar_Pervasives_Native.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____2703 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____2703 c1))
in ((

let uu____2711 = (

let uu____2712 = (

let uu____2713 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____2714 = (

let uu____2715 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____2715))
in (Prims.strcat uu____2713 uu____2714)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____2712))
in (debug_log env uu____2711));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____2728 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____2730 = (

let uu____2731 = (FStar_Syntax_Subst.compress dt1)
in uu____2731.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____2730 ilid num_ibs unfolded env));
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

let uu____2781 = (try_get_fv t1)
in (match (uu____2781) with
| (fv, uu____2787) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____2788 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____2808 = (

let uu____2809 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____2809))
in (debug_log env uu____2808));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____2811 = (FStar_List.fold_left (fun uu____2828 b -> (match (uu____2828) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____2848 -> begin
(

let uu____2849 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____2862 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____2849), (uu____2862))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____2811) with
| (b, uu____2872) -> begin
b
end)));
)
end
| uu____2873 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____2910 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____2910) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____2932 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____2934 = (

let uu____2935 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____2935))
in (debug_log env uu____2934));
(

let uu____2936 = (

let uu____2937 = (FStar_Syntax_Subst.compress dt)
in uu____2937.FStar_Syntax_Syntax.n)
in (match (uu____2936) with
| FStar_Syntax_Syntax.Tm_fvar (uu____2940) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2943) -> begin
(

let dbs1 = (

let uu____2967 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (FStar_Pervasives_Native.snd uu____2967))
in (

let dbs2 = (

let uu____3005 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____3005 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____3010 = (

let uu____3011 = (

let uu____3012 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____3012 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____3011))
in (debug_log env uu____3010));
(

let uu____3017 = (FStar_List.fold_left (fun uu____3034 b -> (match (uu____3034) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3054 -> begin
(

let uu____3055 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3068 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3055), (uu____3068))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____3017) with
| (b, uu____3078) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____3079, uu____3080) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____3102 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____3130 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____3146, uu____3147, uu____3148) -> begin
((lid), (us), (bs))
end
| uu____3157 -> begin
(failwith "Impossible!")
end)
in (match (uu____3130) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____3167 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____3167) with
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

let uu____3190 = (

let uu____3193 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (FStar_Pervasives_Native.snd uu____3193))
in (FStar_List.for_all (fun d -> (

let uu____3205 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____3205 unfolded_inductives env2))) uu____3190))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3226, uu____3227, t, uu____3229, uu____3230, uu____3231) -> begin
t
end
| uu____3236 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____3259 = (

let uu____3260 = (FStar_Syntax_Subst.compress dt1)
in uu____3260.FStar_Syntax_Syntax.n)
in (match (uu____3259) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3264) -> begin
(

let dbs1 = (

let uu____3288 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____3288))
in (

let dbs2 = (

let uu____3326 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____3326 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____3341 = (

let uu____3342 = (

let uu____3343 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____3343)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____3342))
in (uu____3341 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sort_range = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____3348 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____3348 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____3356 = (

let uu____3357 = (

let uu____3358 = (

let uu____3359 = (

let uu____3360 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____3360 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____3359))
in (uu____3358)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3357))
in (uu____3356 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____3377 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty : FStar_Syntax_Syntax.sigelts  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.sigelt  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____3452 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3474, bs, t, uu____3477, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____3489 -> begin
(failwith "Impossible!")
end)
in (match (uu____3452) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____3528 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____3528 t))
in (

let uu____3535 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____3535) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____3567 = (

let uu____3568 = (FStar_Syntax_Subst.compress t2)
in uu____3568.FStar_Syntax_Syntax.n)
in (match (uu____3567) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3578) -> begin
ibs
end
| uu____3595 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____3602 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____3603 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3602 uu____3603)))
in (

let ind1 = (

let uu____3609 = (

let uu____3610 = (FStar_List.map (fun uu____3623 -> (match (uu____3623) with
| (bv, aq) -> begin
(

let uu____3634 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____3634), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____3610))
in (uu____3609 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____3640 = (

let uu____3641 = (FStar_List.map (fun uu____3654 -> (match (uu____3654) with
| (bv, aq) -> begin
(

let uu____3665 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____3665), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3641))
in (uu____3640 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____3671 = (

let uu____3672 = (

let uu____3673 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____3673)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____3672))
in (uu____3671 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____3699 = acc
in (match (uu____3699) with
| (uu____3714, en, uu____3716, uu____3717) -> begin
(

let opt = (

let uu____3733 = (

let uu____3734 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____3734))
in (FStar_TypeChecker_Rel.try_subtype' en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____3733 false))
in (match (opt) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____3739) -> begin
true
end))
end))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____3746 = (

let uu____3747 = (

let uu____3748 = (

let uu____3749 = (

let uu____3750 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____3750))
in (uu____3749)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____3748))
in (uu____3747 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____3746))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___95_3757 = fml
in (

let uu____3758 = (

let uu____3759 = (

let uu____3766 = (

let uu____3767 = (

let uu____3778 = (

let uu____3781 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____3781)::[])
in (uu____3778)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____3767))
in ((fml), (uu____3766)))
in FStar_Syntax_Syntax.Tm_meta (uu____3759))
in {FStar_Syntax_Syntax.n = uu____3758; FStar_Syntax_Syntax.pos = uu___95_3757.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___95_3757.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____3794 = (

let uu____3795 = (

let uu____3796 = (

let uu____3797 = (

let uu____3798 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____3798 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____3797))
in (uu____3796)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3795))
in (uu____3794 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____3823 = (

let uu____3824 = (

let uu____3825 = (

let uu____3826 = (

let uu____3827 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____3827 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____3826))
in (uu____3825)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3824))
in (uu____3823 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml3)
in (

let uu____3847 = acc
in (match (uu____3847) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs2)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs1)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3909, uu____3910, uu____3911, t_lid, uu____3913, uu____3914) -> begin
(t_lid = lid)
end
| uu____3919 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____3926 = (optimized_haseq_soundness_for_data lid d usubst bs2)
in (FStar_Syntax_Util.mk_conj acc1 uu____3926))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____3928 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____3931 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml3)))::[]))), (env2), (uu____3928), (uu____3931)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4019, us, uu____4021, uu____4022, uu____4023, uu____4024) -> begin
us
end
| uu____4033 -> begin
(failwith "Impossible!")
end))
in (

let uu____4034 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4034) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____4059 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____4059) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____4117 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____4117) with
| (phi1, uu____4125) -> begin
((

let uu____4127 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____4127) with
| true -> begin
(

let uu____4128 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____4128))
end
| uu____4129 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____4145 -> (match (uu____4145) with
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


let unoptimized_haseq_data : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun usubst bs haseq_ind mutuals acc data -> (

let rec is_mutual = (fun t -> (

let uu____4203 = (

let uu____4204 = (FStar_Syntax_Subst.compress t)
in uu____4204.FStar_Syntax_Syntax.n)
in (match (uu____4203) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____4211) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____4244 = (is_mutual t')
in (match (uu____4244) with
| true -> begin
true
end
| uu____4245 -> begin
(

let uu____4246 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (exists_mutual uu____4246))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____4262) -> begin
(is_mutual t')
end
| uu____4267 -> begin
false
end)))
and exists_mutual = (fun uu___87_4268 -> (match (uu___87_4268) with
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

let uu____4287 = (

let uu____4288 = (FStar_Syntax_Subst.compress dt1)
in uu____4288.FStar_Syntax_Syntax.n)
in (match (uu____4287) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4294) -> begin
(

let dbs1 = (

let uu____4318 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____4318))
in (

let dbs2 = (

let uu____4356 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____4356 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____4374 = (

let uu____4375 = (

let uu____4376 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____4376)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4375))
in (uu____4374 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____4380 = (is_mutual sort)
in (match (uu____4380) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____4381 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____4390 = (

let uu____4391 = (

let uu____4392 = (

let uu____4393 = (

let uu____4394 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4394 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4393))
in (uu____4392)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4391))
in (uu____4390 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____4411 -> begin
acc
end))))))


let unoptimized_haseq_ty : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____4454 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4476, bs, t, uu____4479, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____4491 -> begin
(failwith "Impossible!")
end)
in (match (uu____4454) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____4514 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____4514 t))
in (

let uu____4521 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____4521) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____4537 = (

let uu____4538 = (FStar_Syntax_Subst.compress t2)
in uu____4538.FStar_Syntax_Syntax.n)
in (match (uu____4537) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4548) -> begin
ibs
end
| uu____4565 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____4572 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____4573 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4572 uu____4573)))
in (

let ind1 = (

let uu____4579 = (

let uu____4580 = (FStar_List.map (fun uu____4593 -> (match (uu____4593) with
| (bv, aq) -> begin
(

let uu____4604 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4604), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4580))
in (uu____4579 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____4610 = (

let uu____4611 = (FStar_List.map (fun uu____4624 -> (match (uu____4624) with
| (bv, aq) -> begin
(

let uu____4635 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4635), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4611))
in (uu____4610 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____4641 = (

let uu____4642 = (

let uu____4643 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____4643)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4642))
in (uu____4641 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4657, uu____4658, uu____4659, t_lid, uu____4661, uu____4662) -> begin
(t_lid = lid)
end
| uu____4667 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___96_4673 = fml
in (

let uu____4674 = (

let uu____4675 = (

let uu____4682 = (

let uu____4683 = (

let uu____4694 = (

let uu____4697 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____4697)::[])
in (uu____4694)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____4683))
in ((fml), (uu____4682)))
in FStar_Syntax_Syntax.Tm_meta (uu____4675))
in {FStar_Syntax_Syntax.n = uu____4674; FStar_Syntax_Syntax.pos = uu___96_4673.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___96_4673.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____4710 = (

let uu____4711 = (

let uu____4712 = (

let uu____4713 = (

let uu____4714 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4714 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4713))
in (uu____4712)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4711))
in (uu____4710 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____4739 = (

let uu____4740 = (

let uu____4741 = (

let uu____4742 = (

let uu____4743 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4743 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4742))
in (uu____4741)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4740))
in (uu____4739 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4833, uu____4834, uu____4835, uu____4836, uu____4837) -> begin
lid
end
| uu____4846 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____4847 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____4859, uu____4860, uu____4861, uu____4862) -> begin
((lid), (us))
end
| uu____4871 -> begin
(failwith "Impossible!")
end))
in (match (uu____4847) with
| (lid, us) -> begin
(

let uu____4880 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4880) with
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

let uu____4907 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env1 uu____4907 fml [] FStar_Range.dummyRange))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____4957 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___88_4982 -> (match (uu___88_4982) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____4983); FStar_Syntax_Syntax.sigrng = uu____4984; FStar_Syntax_Syntax.sigquals = uu____4985; FStar_Syntax_Syntax.sigmeta = uu____4986; FStar_Syntax_Syntax.sigattrs = uu____4987} -> begin
true
end
| uu____5008 -> begin
false
end))))
in (match (uu____4957) with
| (tys, datas) -> begin
((

let uu____5030 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___89_5039 -> (match (uu___89_5039) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5040); FStar_Syntax_Syntax.sigrng = uu____5041; FStar_Syntax_Syntax.sigquals = uu____5042; FStar_Syntax_Syntax.sigmeta = uu____5043; FStar_Syntax_Syntax.sigattrs = uu____5044} -> begin
false
end
| uu____5063 -> begin
true
end))))
in (match (uu____5030) with
| true -> begin
(

let uu____5064 = (

let uu____5065 = (

let uu____5070 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____5070)))
in FStar_Errors.Error (uu____5065))
in (FStar_Exn.raise uu____5064))
end
| uu____5071 -> begin
()
end));
(

let env0 = env
in (

let uu____5073 = (FStar_List.fold_right (fun tc uu____5112 -> (match (uu____5112) with
| (env1, all_tcs, g) -> begin
(

let uu____5152 = (tc_tycon env1 tc)
in (match (uu____5152) with
| (env2, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____5179 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____5179) with
| true -> begin
(

let uu____5180 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____5180))
end
| uu____5181 -> begin
()
end));
(

let uu____5182 = (

let uu____5183 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____5183))
in ((env2), ((((tc1), (tc_u)))::all_tcs), (uu____5182)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____5073) with
| (env1, tcs, g) -> begin
(

let uu____5229 = (FStar_List.fold_right (fun se uu____5251 -> (match (uu____5251) with
| (datas1, g1) -> begin
(

let uu____5270 = (

let uu____5275 = (tc_data env1 tcs)
in (uu____5275 se))
in (match (uu____5270) with
| (data, g') -> begin
(

let uu____5290 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas1), (uu____5290)))
end))
end)) datas (([]), (g)))
in (match (uu____5229) with
| (datas1, g1) -> begin
(

let uu____5311 = (generalize_and_inst_within env0 g1 tcs datas1)
in (match (uu____5311) with
| (tcs1, datas2) -> begin
(

let sig_bndle = (

let uu____5341 = (FStar_TypeChecker_Env.get_range env0)
in (

let uu____5342 = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) ses)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas2)), (lids))); FStar_Syntax_Syntax.sigrng = uu____5341; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = uu____5342}))
in ((sig_bndle), (tcs1), (datas2)))
end))
end))
end)));
)
end)))




