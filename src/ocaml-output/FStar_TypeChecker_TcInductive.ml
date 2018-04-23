
open Prims
open FStar_Pervasives

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data) -> begin
(

let env0 = env
in (

let uu____42 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____42) with
| (usubst, uvs1) -> begin
(

let uu____69 = (

let uu____76 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let uu____77 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let uu____78 = (

let uu____79 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps) usubst)
in (FStar_Syntax_Subst.subst uu____79 k))
in ((uu____76), (uu____77), (uu____78)))))
in (match (uu____69) with
| (env1, tps1, k1) -> begin
(

let uu____97 = (FStar_Syntax_Subst.open_term tps1 k1)
in (match (uu____97) with
| (tps2, k2) -> begin
(

let uu____112 = (FStar_TypeChecker_TcTerm.tc_binders env1 tps2)
in (match (uu____112) with
| (tps3, env_tps, guard_params, us) -> begin
(

let k3 = (FStar_TypeChecker_Normalize.unfold_whnf env1 k2)
in (

let uu____134 = (FStar_Syntax_Util.arrow_formals k3)
in (match (uu____134) with
| (indices, t) -> begin
(

let uu____173 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____173) with
| (indices1, env', guard_indices, us') -> begin
(

let uu____194 = (

let uu____199 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____199) with
| (t1, uu____211, g) -> begin
(

let uu____213 = (

let uu____214 = (

let uu____215 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____215))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____214))
in ((t1), (uu____213)))
end))
in (match (uu____194) with
| (t1, guard) -> begin
(

let k4 = (

let uu____229 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow indices1 uu____229))
in (

let uu____232 = (FStar_Syntax_Util.type_u ())
in (match (uu____232) with
| (t_type, u) -> begin
((

let uu____248 = (FStar_TypeChecker_Rel.teq env' t1 t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____248));
(

let usubst1 = (FStar_Syntax_Subst.univ_var_closing uvs1)
in (

let t_tc = (

let uu____255 = (

let uu____262 = (FStar_All.pipe_right tps3 (FStar_Syntax_Subst.subst_binders usubst1))
in (

let uu____275 = (

let uu____282 = (

let uu____293 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps3) usubst1)
in (FStar_Syntax_Subst.subst_binders uu____293))
in (FStar_All.pipe_right indices1 uu____282))
in (FStar_List.append uu____262 uu____275)))
in (

let uu____310 = (

let uu____313 = (

let uu____314 = (

let uu____319 = (FStar_Syntax_Subst.shift_subst ((FStar_List.length tps3) + (FStar_List.length indices1)) usubst1)
in (FStar_Syntax_Subst.subst uu____319))
in (FStar_All.pipe_right t1 uu____314))
in (FStar_Syntax_Syntax.mk_Total uu____313))
in (FStar_Syntax_Util.arrow uu____255 uu____310)))
in (

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let k5 = (FStar_Syntax_Subst.close tps4 k4)
in (

let uu____332 = (

let uu____337 = (FStar_Syntax_Subst.subst_binders usubst1 tps4)
in (

let uu____338 = (

let uu____339 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps4) usubst1)
in (FStar_Syntax_Subst.subst uu____339 k5))
in ((uu____337), (uu____338))))
in (match (uu____332) with
| (tps5, k6) -> begin
(

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____357 = (FStar_TypeChecker_Env.push_let_binding env0 (FStar_Util.Inr (fv_tc)) ((uvs1), (t_tc)))
in ((uu____357), ((

let uu___73_363 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps5), (k6), (mutuals), (data))); FStar_Syntax_Syntax.sigrng = uu___73_363.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___73_363.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___73_363.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___73_363.FStar_Syntax_Syntax.sigattrs})), (u), (guard))))
end))))));
)
end)))
end))
end))
end)))
end))
end))
end))
end)))
end
| uu____368 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, _mutual_tcs) -> begin
(

let uu____428 = (FStar_Syntax_Subst.univ_var_opening _uvs)
in (match (uu____428) with
| (usubst, _uvs1) -> begin
(

let uu____451 = (

let uu____456 = (FStar_TypeChecker_Env.push_univ_vars env _uvs1)
in (

let uu____457 = (FStar_Syntax_Subst.subst usubst t)
in ((uu____456), (uu____457))))
in (match (uu____451) with
| (env1, t1) -> begin
(

let uu____464 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____503 -> (match (uu____503) with
| (se1, u_tc) -> begin
(

let uu____518 = (

let uu____519 = (

let uu____520 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____520))
in (FStar_Ident.lid_equals tc_lid uu____519))
in (match (uu____518) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____539, uu____540, tps, uu____542, uu____543, uu____544) -> begin
(

let tps1 = (

let uu____554 = (FStar_All.pipe_right tps (FStar_Syntax_Subst.subst_binders usubst))
in (FStar_All.pipe_right uu____554 (FStar_List.map (fun uu____586 -> (match (uu____586) with
| (x, uu____598) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____602 = (

let uu____609 = (FStar_TypeChecker_Env.push_binders env1 tps2)
in ((uu____609), (tps2), (u_tc)))
in FStar_Pervasives_Native.Some (uu____602))))
end
| uu____616 -> begin
(failwith "Impossible")
end)
end
| uu____625 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (tps_u_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____657 = (FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid)
in (match (uu____657) with
| true -> begin
((env1), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____668 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____464) with
| (env2, tps, u_tc) -> begin
(

let uu____682 = (

let t2 = (FStar_TypeChecker_Normalize.unfold_whnf env2 t1)
in (

let uu____696 = (

let uu____697 = (FStar_Syntax_Subst.compress t2)
in uu____697.FStar_Syntax_Syntax.n)
in (match (uu____696) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____730 = (FStar_Util.first_N ntps bs)
in (match (uu____730) with
| (uu____763, bs') -> begin
(

let t3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____820 -> (match (uu____820) with
| (x, uu____826) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____827 = (FStar_Syntax_Subst.subst subst1 t3)
in (FStar_Syntax_Util.arrow_formals uu____827))))
end))
end
| uu____828 -> begin
(([]), (t2))
end)))
in (match (uu____682) with
| (arguments, result) -> begin
((

let uu____862 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____862) with
| true -> begin
(

let uu____863 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____864 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____865 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____863 uu____864 uu____865))))
end
| uu____866 -> begin
()
end));
(

let uu____867 = (FStar_TypeChecker_TcTerm.tc_tparams env2 arguments)
in (match (uu____867) with
| (arguments1, env', us) -> begin
(

let uu____881 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____881) with
| (result1, res_lcomp) -> begin
((

let uu____893 = (

let uu____894 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____894.FStar_Syntax_Syntax.n)
in (match (uu____893) with
| FStar_Syntax_Syntax.Tm_type (uu____897) -> begin
()
end
| ty -> begin
(

let uu____899 = (

let uu____904 = (

let uu____905 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____906 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____905 uu____906)))
in ((FStar_Errors.Fatal_WrongResultTypeAfterConstrutor), (uu____904)))
in (FStar_Errors.raise_error uu____899 se.FStar_Syntax_Syntax.sigrng))
end));
(

let uu____907 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____907) with
| (head1, uu____927) -> begin
(

let g_uvs = (

let uu____949 = (

let uu____950 = (FStar_Syntax_Subst.compress head1)
in uu____950.FStar_Syntax_Syntax.n)
in (match (uu____949) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____954; FStar_Syntax_Syntax.vars = uu____955}, tuvs) -> begin
(match ((Prims.op_Equality (FStar_List.length _uvs1) (FStar_List.length tuvs))) with
| true -> begin
(FStar_List.fold_left2 (fun g u1 u2 -> (

let uu____968 = (

let uu____969 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____970 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u2))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_TypeChecker_Rel.teq env' uu____969 uu____970)))
in (FStar_TypeChecker_Rel.conj_guard g uu____968))) FStar_TypeChecker_Rel.trivial_guard tuvs _uvs1)
end
| uu____971 -> begin
(failwith "Impossible: tc_datacon: length of annotated universes not same as instantiated ones")
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| uu____973 -> begin
(

let uu____974 = (

let uu____979 = (

let uu____980 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____981 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____980 uu____981)))
in ((FStar_Errors.Fatal_UnexpectedConstructorType), (uu____979)))
in (FStar_Errors.raise_error uu____974 se.FStar_Syntax_Syntax.sigrng))
end))
in (

let g = (FStar_List.fold_left2 (fun g uu____994 u_x -> (match (uu____994) with
| (x, uu____1001) -> begin
(

let uu____1002 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____1002))
end)) g_uvs arguments1 us)
in (

let t2 = (

let uu____1006 = (

let uu____1013 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____1045 -> (match (uu____1045) with
| (x, uu____1057) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____1013 arguments1))
in (

let uu____1064 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____1006 uu____1064)))
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars _uvs1 t2)
in (((

let uu___74_1069 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), (_uvs1), (t3), (tc_lid), (ntps), ([]))); FStar_Syntax_Syntax.sigrng = uu___74_1069.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___74_1069.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___74_1069.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___74_1069.FStar_Syntax_Syntax.sigattrs})), (g))))))
end));
)
end))
end));
)
end))
end))
end))
end))
end
| uu____1072 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map FStar_Pervasives_Native.snd tcs)
in (

let g1 = (

let uu___75_1137 = g
in {FStar_TypeChecker_Env.guard_f = uu___75_1137.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___75_1137.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((FStar_Pervasives_Native.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___75_1137.FStar_TypeChecker_Env.implicits})
in ((

let uu____1147 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1147) with
| true -> begin
(

let uu____1148 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____1148))
end
| uu____1149 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____1176 -> (match (uu____1176) with
| (se, uu____1182) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1183, uu____1184, tps, k, uu____1187, uu____1188) -> begin
(

let uu____1197 = (

let uu____1198 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____1198))
in (FStar_Syntax_Syntax.null_binder uu____1197))
end
| uu____1203 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1227, uu____1228, t, uu____1230, uu____1231, uu____1232) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____1237 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____1241 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____1241))
in ((

let uu____1249 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1249) with
| true -> begin
(

let uu____1250 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____1250))
end
| uu____1251 -> begin
()
end));
(

let uu____1252 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____1252) with
| (uvs, t1) -> begin
((

let uu____1272 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1272) with
| true -> begin
(

let uu____1273 = (

let uu____1274 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____1274 (FStar_String.concat ", ")))
in (

let uu____1285 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____1273 uu____1285)))
end
| uu____1286 -> begin
()
end));
(

let uu____1287 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____1287) with
| (uvs1, t2) -> begin
(

let uu____1302 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____1302) with
| (args, uu____1324) -> begin
(

let uu____1341 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____1341) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____1424 uu____1425 -> (match (((uu____1424), (uu____1425))) with
| ((x, uu____1443), (se, uu____1445)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1455, tps, uu____1457, mutuals, datas1) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____1469 = (

let uu____1474 = (

let uu____1475 = (FStar_Syntax_Subst.compress ty)
in uu____1475.FStar_Syntax_Syntax.n)
in (match (uu____1474) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____1500 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____1500) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1564 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos)
end)
in ((tps1), (t3)))
end))
end
| uu____1587 -> begin
(([]), (ty))
end))
in (match (uu____1469) with
| (tps1, t3) -> begin
(

let uu___76_1600 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1))); FStar_Syntax_Syntax.sigrng = uu___76_1600.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___76_1600.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___76_1600.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___76_1600.FStar_Syntax_Syntax.sigattrs})
end)))
end
| uu____1605 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____1611 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_17 -> FStar_Syntax_Syntax.U_name (_0_17))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___64_1639 -> (match (uu___64_1639) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1647, uu____1648, uu____1649, uu____1650, uu____1651); FStar_Syntax_Syntax.sigrng = uu____1652; FStar_Syntax_Syntax.sigquals = uu____1653; FStar_Syntax_Syntax.sigmeta = uu____1654; FStar_Syntax_Syntax.sigattrs = uu____1655} -> begin
((tc), (uvs_universes))
end
| uu____1670 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____1693 d -> (match (uu____1693) with
| (t3, uu____1700) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____1702, uu____1703, tc, ntps, mutuals) -> begin
(

let ty = (

let uu____1712 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____1712 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___77_1713 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___77_1713.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___77_1713.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___77_1713.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___77_1713.FStar_Syntax_Syntax.sigattrs}))
end
| uu____1716 -> begin
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


let debug_log : FStar_TypeChecker_Env.env_t  ->  Prims.string  ->  unit = (fun env s -> (

let uu____1731 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____1731) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____1732 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____1743 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____1743)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____1759 = (

let uu____1760 = (FStar_Syntax_Subst.compress t)
in uu____1760.FStar_Syntax_Syntax.n)
in (match (uu____1759) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____1779 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____1784 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1837 = (FStar_ST.op_Bang unfolded)
in (FStar_List.existsML (fun uu____1906 -> (match (uu____1906) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1941 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (FStar_Pervasives_Native.fst uu____1941))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst a')))) true args l)))
end)) uu____1837)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____2161 = (

let uu____2162 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____2162))
in (debug_log env uu____2161));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____2165 = (

let uu____2166 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____2166))
in (debug_log env uu____2165));
((

let uu____2169 = (ty_occurs_in ty_lid btype1)
in (not (uu____2169))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____2180 = (

let uu____2181 = (FStar_Syntax_Subst.compress btype1)
in uu____2181.FStar_Syntax_Syntax.n)
in (match (uu____2180) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____2206 = (try_get_fv t)
in (match (uu____2206) with
| (fv, us) -> begin
(

let uu____2213 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)
in (match (uu____2213) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____2223 -> (match (uu____2223) with
| (t1, uu____2229) -> begin
(

let uu____2230 = (ty_occurs_in ty_lid t1)
in (not (uu____2230)))
end)) args);
)
end
| uu____2231 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____2272 = (

let uu____2273 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____2273)))
in (match (uu____2272) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____2275 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____2285 -> (match (uu____2285) with
| (b, uu____2291) -> begin
(

let uu____2292 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____2292)))
end)) sbs) && (

let uu____2297 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____2297) with
| (uu____2302, return_type) -> begin
(

let uu____2304 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____2304))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2325) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____2327) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2330) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____2357) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____2383, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____2441 -> (match (uu____2441) with
| (p, uu____2453, t) -> begin
(

let bs = (

let uu____2470 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____2470))
in (

let uu____2477 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2477) with
| (bs1, t1) -> begin
(

let uu____2484 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____2484))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____2506, uu____2507) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____2569 -> begin
((

let uu____2571 = (

let uu____2572 = (

let uu____2573 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____2574 = (

let uu____2575 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____2575))
in (Prims.strcat uu____2573 uu____2574)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____2572))
in (debug_log env uu____2571));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____2593 = (

let uu____2594 = (

let uu____2595 = (

let uu____2596 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____2596))
in (Prims.strcat ilid.FStar_Ident.str uu____2595))
in (Prims.strcat "Checking nested positivity in the inductive " uu____2594))
in (debug_log env uu____2593));
(

let uu____2597 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____2597) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____2611 -> begin
(

let uu____2612 = (already_unfolded ilid args unfolded env)
in (match (uu____2612) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____2634 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____2637 = (

let uu____2638 = (

let uu____2639 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____2639 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____2638))
in (debug_log env uu____2637));
(

let uu____2641 = (

let uu____2642 = (FStar_ST.op_Bang unfolded)
in (

let uu____2692 = (

let uu____2699 = (

let uu____2704 = (

let uu____2713 = (FStar_List.splitAt num_ibs args)
in (FStar_Pervasives_Native.fst uu____2713))
in ((ilid), (uu____2704)))
in (uu____2699)::[])
in (FStar_List.append uu____2642 uu____2692)))
in (FStar_ST.op_Colon_Equals unfolded uu____2641));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____2860 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____2860) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____2882 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____2885 = (

let uu____2886 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____2886))
in (debug_log env uu____2885));
(

let uu____2887 = (

let uu____2888 = (FStar_Syntax_Subst.compress dt1)
in uu____2888.FStar_Syntax_Syntax.n)
in (match (uu____2887) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____2910 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____2910) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____2959 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____2959 dbs1))
in (

let c1 = (

let uu____2963 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____2963 c))
in (

let uu____2966 = (FStar_List.splitAt num_ibs args)
in (match (uu____2966) with
| (args1, uu____2994) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst ib)), ((FStar_Pervasives_Native.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____3066 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____3066 c1))
in ((

let uu____3074 = (

let uu____3075 = (

let uu____3076 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____3077 = (

let uu____3078 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____3078))
in (Prims.strcat uu____3076 uu____3077)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____3075))
in (debug_log env uu____3074));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____3107 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____3109 = (

let uu____3110 = (FStar_Syntax_Subst.compress dt1)
in uu____3110.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____3109 ilid num_ibs unfolded env));
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

let uu____3172 = (try_get_fv t1)
in (match (uu____3172) with
| (fv, uu____3178) -> begin
(

let uu____3179 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)
in (match (uu____3179) with
| true -> begin
true
end
| uu____3180 -> begin
(failwith "Impossible, expected the type to be ilid")
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____3200 = (

let uu____3201 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____3201))
in (debug_log env uu____3200));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____3203 = (FStar_List.fold_left (fun uu____3220 b -> (match (uu____3220) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3240 -> begin
(

let uu____3241 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3262 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3241), (uu____3262))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____3203) with
| (b, uu____3272) -> begin
b
end)));
)
end
| uu____3273 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____3324 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3324) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3346 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____3348 = (

let uu____3349 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____3349))
in (debug_log env uu____3348));
(

let uu____3350 = (

let uu____3351 = (FStar_Syntax_Subst.compress dt)
in uu____3351.FStar_Syntax_Syntax.n)
in (match (uu____3350) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3354) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3357) -> begin
(

let dbs1 = (

let uu____3381 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (FStar_Pervasives_Native.snd uu____3381))
in (

let dbs2 = (

let uu____3419 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____3419 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____3424 = (

let uu____3425 = (

let uu____3426 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____3426 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____3425))
in (debug_log env uu____3424));
(

let uu____3431 = (FStar_List.fold_left (fun uu____3448 b -> (match (uu____3448) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3468 -> begin
(

let uu____3469 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3490 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3469), (uu____3490))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____3431) with
| (b, uu____3500) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____3501, uu____3502) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, univs1) -> begin
((debug_log env "Data constructor type is a Tm_uinst, so recursing in the base type");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____3551 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____3569 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____3585, uu____3586, uu____3587) -> begin
((lid), (us), (bs))
end
| uu____3596 -> begin
(failwith "Impossible!")
end)
in (match (uu____3569) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____3606 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____3606) with
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

let uu____3629 = (

let uu____3632 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (FStar_Pervasives_Native.snd uu____3632))
in (FStar_List.for_all (fun d -> (

let uu____3644 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____3644 unfolded_inductives env2))) uu____3629))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3674, uu____3675, t, uu____3677, uu____3678, uu____3679) -> begin
t
end
| uu____3684 -> begin
(failwith "Impossible!")
end))


let haseq_suffix : Prims.string = "__uu___haseq"


let is_haseq_lid : FStar_Ident.lid  ->  Prims.bool = (fun lid -> (

let str = lid.FStar_Ident.str
in (

let len = (FStar_String.length str)
in (

let haseq_suffix_len = (FStar_String.length haseq_suffix)
in ((len > haseq_suffix_len) && (

let uu____3704 = (

let uu____3705 = (FStar_String.substring str (len - haseq_suffix_len) haseq_suffix_len)
in (FStar_String.compare uu____3705 haseq_suffix))
in (Prims.op_Equality uu____3704 (Prims.parse_int "0"))))))))


let get_haseq_axiom_lid : FStar_Ident.lid  ->  FStar_Ident.lid = (fun lid -> (

let uu____3725 = (

let uu____3728 = (

let uu____3731 = (FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText haseq_suffix))
in (uu____3731)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____3728))
in (FStar_Ident.lid_of_ids uu____3725)))


let get_optimized_haseq_axiom : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_names  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun en ty usubst us -> (

let uu____3776 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3790, bs, t, uu____3793, uu____3794) -> begin
((lid), (bs), (t))
end
| uu____3803 -> begin
(failwith "Impossible!")
end)
in (match (uu____3776) with
| (lid, bs, t) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____3825 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____3825 t))
in (

let uu____3832 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____3832) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____3850 = (

let uu____3851 = (FStar_Syntax_Subst.compress t2)
in uu____3851.FStar_Syntax_Syntax.n)
in (match (uu____3850) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3855) -> begin
ibs
end
| uu____3872 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____3879 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____3880 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3879 uu____3880)))
in (

let ind1 = (

let uu____3886 = (

let uu____3891 = (FStar_List.map (fun uu____3904 -> (match (uu____3904) with
| (bv, aq) -> begin
(

let uu____3915 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____3915), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____3891))
in (uu____3886 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____3921 = (

let uu____3926 = (FStar_List.map (fun uu____3939 -> (match (uu____3939) with
| (bv, aq) -> begin
(

let uu____3950 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____3950), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____3926))
in (uu____3921 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____3956 = (

let uu____3961 = (

let uu____3962 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____3962)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____3961))
in (uu____3956 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____4001 = (

let uu____4002 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____4002))
in (FStar_TypeChecker_Rel.subtype_nosmt en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____4001))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____4013 = (

let uu____4014 = (

let uu____4019 = (

let uu____4020 = (

let uu____4027 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____4027))
in (uu____4020)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4019))
in (uu____4014 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____4013))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___78_4046 = fml
in (

let uu____4047 = (

let uu____4048 = (

let uu____4055 = (

let uu____4056 = (

let uu____4067 = (

let uu____4076 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____4076)::[])
in (uu____4067)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____4056))
in ((fml), (uu____4055)))
in FStar_Syntax_Syntax.Tm_meta (uu____4048))
in {FStar_Syntax_Syntax.n = uu____4047; FStar_Syntax_Syntax.pos = uu___78_4046.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___78_4046.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____4103 = (

let uu____4108 = (

let uu____4109 = (

let uu____4116 = (

let uu____4117 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4117 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4116))
in (uu____4109)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4108))
in (uu____4103 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____4158 = (

let uu____4163 = (

let uu____4164 = (

let uu____4171 = (

let uu____4172 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4172 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4171))
in (uu____4164)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4163))
in (uu____4158 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (

let axiom_lid = (get_haseq_axiom_lid lid)
in ((axiom_lid), (fml3), (bs2), (ibs1), (haseq_bs)))))))))))))))
end))))
end)))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____4232 = (

let uu____4233 = (FStar_Syntax_Subst.compress dt1)
in uu____4233.FStar_Syntax_Syntax.n)
in (match (uu____4232) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4237) -> begin
(

let dbs1 = (

let uu____4261 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____4261))
in (

let dbs2 = (

let uu____4299 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____4299 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____4314 = (

let uu____4319 = (

let uu____4320 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____4320)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4319))
in (uu____4314 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sort_range = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____4343 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____4343 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____4351 = (

let uu____4356 = (

let uu____4357 = (

let uu____4364 = (

let uu____4365 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4365 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4364))
in (uu____4357)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4356))
in (uu____4351 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____4398 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty : FStar_Syntax_Syntax.sigelts  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.sigelt  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun all_datas_in_the_bundle usubst us acc ty -> (

let lid = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4488, uu____4489, uu____4490, uu____4491, uu____4492) -> begin
lid
end
| uu____4501 -> begin
(failwith "Impossible!")
end)
in (

let uu____4502 = acc
in (match (uu____4502) with
| (uu____4539, en, uu____4541, uu____4542) -> begin
(

let uu____4563 = (get_optimized_haseq_axiom en ty usubst us)
in (match (uu____4563) with
| (axiom_lid, fml, bs, ibs, haseq_bs) -> begin
(

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____4600 = acc
in (match (uu____4600) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4674, uu____4675, uu____4676, t_lid, uu____4678, uu____4679) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____4684 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____4697 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc1 uu____4697))) FStar_Syntax_Util.t_true t_datas)
in (

let uu____4698 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____4701 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env2), (uu____4698), (uu____4701))))))))
end)))
end))
end))))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4760, us, uu____4762, uu____4763, uu____4764, uu____4765) -> begin
us
end
| uu____4774 -> begin
(failwith "Impossible!")
end))
in (

let uu____4775 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4775) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____4800 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____4800) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____4866 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____4866) with
| (phi1, uu____4874) -> begin
((

let uu____4876 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____4876) with
| true -> begin
(

let uu____4877 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____4877))
end
| uu____4878 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____4894 -> (match (uu____4894) with
| (lid, fml) -> begin
(

let fml1 = (FStar_Syntax_Subst.close_univ_vars us1 fml)
in (FStar_List.append l (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (us1), (fml1))); FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})::[])))
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

let uu____4962 = (

let uu____4963 = (FStar_Syntax_Subst.compress t)
in uu____4963.FStar_Syntax_Syntax.n)
in (match (uu____4962) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____4970) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____5003 = (is_mutual t')
in (match (uu____5003) with
| true -> begin
true
end
| uu____5004 -> begin
(

let uu____5005 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (exists_mutual uu____5005))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____5021) -> begin
(is_mutual t')
end
| uu____5026 -> begin
false
end)))
and exists_mutual = (fun uu___65_5027 -> (match (uu___65_5027) with
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

let uu____5046 = (

let uu____5047 = (FStar_Syntax_Subst.compress dt1)
in uu____5047.FStar_Syntax_Syntax.n)
in (match (uu____5046) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5053) -> begin
(

let dbs1 = (

let uu____5077 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____5077))
in (

let dbs2 = (

let uu____5115 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5115 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____5133 = (

let uu____5138 = (

let uu____5139 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____5139)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5138))
in (uu____5133 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____5161 = (is_mutual sort)
in (match (uu____5161) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____5162 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____5171 = (

let uu____5176 = (

let uu____5177 = (

let uu____5184 = (

let uu____5185 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____5185 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____5184))
in (uu____5177)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5176))
in (uu____5171 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____5218 -> begin
acc
end))))))


let unoptimized_haseq_ty : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____5267 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5289, bs, t, uu____5292, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____5304 -> begin
(failwith "Impossible!")
end)
in (match (uu____5267) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____5327 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____5327 t))
in (

let uu____5334 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____5334) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____5344 = (

let uu____5345 = (FStar_Syntax_Subst.compress t2)
in uu____5345.FStar_Syntax_Syntax.n)
in (match (uu____5344) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5349) -> begin
ibs
end
| uu____5366 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____5373 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____5374 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5373 uu____5374)))
in (

let ind1 = (

let uu____5380 = (

let uu____5385 = (FStar_List.map (fun uu____5398 -> (match (uu____5398) with
| (bv, aq) -> begin
(

let uu____5409 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5409), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____5385))
in (uu____5380 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____5415 = (

let uu____5420 = (FStar_List.map (fun uu____5433 -> (match (uu____5433) with
| (bv, aq) -> begin
(

let uu____5444 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5444), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____5420))
in (uu____5415 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____5450 = (

let uu____5455 = (

let uu____5456 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____5456)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5455))
in (uu____5450 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5488, uu____5489, uu____5490, t_lid, uu____5492, uu____5493) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____5498 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___79_5504 = fml
in (

let uu____5505 = (

let uu____5506 = (

let uu____5513 = (

let uu____5514 = (

let uu____5525 = (

let uu____5534 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____5534)::[])
in (uu____5525)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____5514))
in ((fml), (uu____5513)))
in FStar_Syntax_Syntax.Tm_meta (uu____5506))
in {FStar_Syntax_Syntax.n = uu____5505; FStar_Syntax_Syntax.pos = uu___79_5504.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___79_5504.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____5561 = (

let uu____5566 = (

let uu____5567 = (

let uu____5574 = (

let uu____5575 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____5575 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____5574))
in (uu____5567)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5566))
in (uu____5561 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____5616 = (

let uu____5621 = (

let uu____5622 = (

let uu____5629 = (

let uu____5630 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____5630 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____5629))
in (uu____5622)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5621))
in (uu____5616 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5707, uu____5708, uu____5709, uu____5710, uu____5711) -> begin
lid
end
| uu____5720 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____5721 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____5733, uu____5734, uu____5735, uu____5736) -> begin
((lid), (us))
end
| uu____5745 -> begin
(failwith "Impossible!")
end))
in (match (uu____5721) with
| (lid, us) -> begin
(

let uu____5754 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5754) with
| (usubst, us1) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us1) FStar_Syntax_Util.t_true tcs)
in (

let se = (

let uu____5777 = (

let uu____5778 = (

let uu____5785 = (get_haseq_axiom_lid lid)
in ((uu____5785), (us1), (fml)))
in FStar_Syntax_Syntax.Sig_assume (uu____5778))
in {FStar_Syntax_Syntax.sigel = uu____5777; FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (se)::[]))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____5838 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___66_5863 -> (match (uu___66_5863) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____5864); FStar_Syntax_Syntax.sigrng = uu____5865; FStar_Syntax_Syntax.sigquals = uu____5866; FStar_Syntax_Syntax.sigmeta = uu____5867; FStar_Syntax_Syntax.sigattrs = uu____5868} -> begin
true
end
| uu____5889 -> begin
false
end))))
in (match (uu____5838) with
| (tys, datas) -> begin
((

let uu____5911 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___67_5920 -> (match (uu___67_5920) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5921); FStar_Syntax_Syntax.sigrng = uu____5922; FStar_Syntax_Syntax.sigquals = uu____5923; FStar_Syntax_Syntax.sigmeta = uu____5924; FStar_Syntax_Syntax.sigattrs = uu____5925} -> begin
false
end
| uu____5944 -> begin
true
end))))
in (match (uu____5911) with
| true -> begin
(

let uu____5945 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType), ("Mutually defined type contains a non-inductive element")) uu____5945))
end
| uu____5946 -> begin
()
end));
(

let univs1 = (match ((Prims.op_Equality (FStar_List.length tys) (Prims.parse_int "0"))) with
| true -> begin
[]
end
| uu____5952 -> begin
(

let uu____5953 = (

let uu____5954 = (FStar_List.hd tys)
in uu____5954.FStar_Syntax_Syntax.sigel)
in (match (uu____5953) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5957, uvs, uu____5959, uu____5960, uu____5961, uu____5962) -> begin
uvs
end
| uu____5971 -> begin
(failwith "Impossible, can\'t happen!")
end))
end)
in (

let env0 = env
in (

let uu____5975 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
((env), (tys), (datas))
end
| uu____6000 -> begin
(

let uu____6001 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____6001) with
| (subst1, univs2) -> begin
(

let tys1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6039, bs, t, l1, l2) -> begin
(

let uu____6052 = (

let uu____6069 = (FStar_Syntax_Subst.subst_binders subst1 bs)
in (

let uu____6070 = (

let uu____6071 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) subst1)
in (FStar_Syntax_Subst.subst uu____6071 t))
in ((lid), (univs2), (uu____6069), (uu____6070), (l1), (l2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____6052))
end
| uu____6082 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___80_6083 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___80_6083.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___80_6083.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___80_6083.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___80_6083.FStar_Syntax_Syntax.sigattrs}))) tys)
in (

let datas1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6093, t, lid_t, x, l) -> begin
(

let uu____6102 = (

let uu____6117 = (FStar_Syntax_Subst.subst subst1 t)
in ((lid), (univs2), (uu____6117), (lid_t), (x), (l)))
in FStar_Syntax_Syntax.Sig_datacon (uu____6102))
end
| uu____6120 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___81_6121 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___81_6121.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___81_6121.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___81_6121.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___81_6121.FStar_Syntax_Syntax.sigattrs}))) datas)
in (

let uu____6122 = (FStar_TypeChecker_Env.push_univ_vars env univs2)
in ((uu____6122), (tys1), (datas1)))))
end))
end)
in (match (uu____5975) with
| (env1, tys1, datas1) -> begin
(

let uu____6148 = (FStar_List.fold_right (fun tc uu____6187 -> (match (uu____6187) with
| (env2, all_tcs, g) -> begin
(

let uu____6227 = (tc_tycon env2 tc)
in (match (uu____6227) with
| (env3, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____6254 = (FStar_TypeChecker_Env.debug env3 FStar_Options.Low)
in (match (uu____6254) with
| true -> begin
(

let uu____6255 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____6255))
end
| uu____6256 -> begin
()
end));
(

let uu____6257 = (

let uu____6258 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____6258))
in ((env3), ((((tc1), (tc_u)))::all_tcs), (uu____6257)));
))
end))
end)) tys1 ((env1), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____6148) with
| (env2, tcs, g) -> begin
(

let uu____6304 = (FStar_List.fold_right (fun se uu____6326 -> (match (uu____6326) with
| (datas2, g1) -> begin
(

let uu____6345 = (

let uu____6350 = (tc_data env2 tcs)
in (uu____6350 se))
in (match (uu____6345) with
| (data, g') -> begin
(

let uu____6367 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas2), (uu____6367)))
end))
end)) datas1 (([]), (g)))
in (match (uu____6304) with
| (datas2, g1) -> begin
(

let uu____6388 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
(generalize_and_inst_within env1 g1 tcs datas2)
end
| uu____6405 -> begin
(

let uu____6406 = (FStar_List.map FStar_Pervasives_Native.fst tcs)
in ((uu____6406), (datas2)))
end)
in (match (uu____6388) with
| (tcs1, datas3) -> begin
(

let sig_bndle = (

let uu____6438 = (FStar_TypeChecker_Env.get_range env0)
in (

let uu____6439 = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) ses)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas3)), (lids))); FStar_Syntax_Syntax.sigrng = uu____6438; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = uu____6439}))
in ((FStar_All.pipe_right tcs1 (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs2, binders, typ, uu____6465, uu____6466) -> begin
(

let fail1 = (fun expected inferred -> (

let uu____6486 = (

let uu____6491 = (

let uu____6492 = (FStar_Syntax_Print.tscheme_to_string expected)
in (

let uu____6493 = (FStar_Syntax_Print.tscheme_to_string inferred)
in (FStar_Util.format2 "Expected an inductive with type %s; got %s" uu____6492 uu____6493)))
in ((FStar_Errors.Fatal_UnexpectedInductivetype), (uu____6491)))
in (FStar_Errors.raise_error uu____6486 se.FStar_Syntax_Syntax.sigrng)))
in (

let uu____6494 = (FStar_TypeChecker_Env.try_lookup_val_decl env0 l)
in (match (uu____6494) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (expected_typ1, uu____6510) -> begin
(

let inferred_typ = (

let body = (match (binders) with
| [] -> begin
typ
end
| uu____6537 -> begin
(

let uu____6538 = (

let uu____6545 = (

let uu____6546 = (

let uu____6559 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____6559)))
in FStar_Syntax_Syntax.Tm_arrow (uu____6546))
in (FStar_Syntax_Syntax.mk uu____6545))
in (uu____6538 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in ((univs2), (body)))
in (match ((Prims.op_Equality (FStar_List.length univs2) (FStar_List.length (FStar_Pervasives_Native.fst expected_typ1)))) with
| true -> begin
(

let uu____6579 = (FStar_TypeChecker_Env.inst_tscheme inferred_typ)
in (match (uu____6579) with
| (uu____6584, inferred) -> begin
(

let uu____6586 = (FStar_TypeChecker_Env.inst_tscheme expected_typ1)
in (match (uu____6586) with
| (uu____6591, expected) -> begin
(

let uu____6593 = (FStar_TypeChecker_Rel.teq_nosmt env0 inferred expected)
in (match (uu____6593) with
| true -> begin
()
end
| uu____6594 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end))
end))
end
| uu____6595 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end)))
end
| uu____6596 -> begin
()
end))));
((sig_bndle), (tcs1), (datas3));
))
end))
end))
end))
end))));
)
end)))


let early_prims_inductives : Prims.string Prims.list = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]


let mk_discriminator_and_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid uvs inductive_tps indices fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (FStar_Pervasives_Native.Some (p)) ptyp))
in (

let inst_univs = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) uvs)
in (

let tps = inductive_tps
in (

let arg_typ = (

let inst_tc = (

let uu____6688 = (

let uu____6695 = (

let uu____6696 = (

let uu____6703 = (

let uu____6706 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____6706))
in ((uu____6703), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____6696))
in (FStar_Syntax_Syntax.mk uu____6695))
in (uu____6688 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6735 -> (match (uu____6735) with
| (x, imp) -> begin
(

let uu____6746 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____6746), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____6748 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____6748))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____6758 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (

let uu____6765 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar uu____6765 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None))
in (

let uu____6766 = (

let uu____6767 = (

let uu____6768 = (

let uu____6773 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____6774 = (

let uu____6775 = (

let uu____6782 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6782))
in (uu____6775)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____6773 uu____6774)))
in (uu____6768 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____6767))
in (FStar_Syntax_Util.refine x uu____6766)))
in (

let uu____6803 = (

let uu___82_6804 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___82_6804.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___82_6804.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____6803)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____6819 = (FStar_List.map (fun uu____6841 -> (match (uu____6841) with
| (x, uu____6853) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____6819 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____6898 -> (match (uu____6898) with
| (x, uu____6910) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let early_prims_inductive = ((

let uu____6916 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____6916)) && ((Prims.op_Equality tc.FStar_Ident.ident.FStar_Ident.idText "dtuple2") || (FStar_List.existsb (fun s -> (Prims.op_Equality s tc.FStar_Ident.ident.FStar_Ident.idText)) early_prims_inductives)))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____6924 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = (early_prims_inductive || (

let uu____6929 = (

let uu____6930 = (FStar_TypeChecker_Env.current_module env)
in uu____6930.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6929)))
in (

let quals = (

let uu____6934 = (FStar_List.filter (fun uu___68_6938 -> (match (uu___68_6938) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____6939 -> begin
false
end)) iquals)
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____6942 -> begin
[]
end)) uu____6934))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____6964 = (

let uu____6965 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____6965))
in (FStar_Syntax_Syntax.mk_Total uu____6964))
in (

let uu____6966 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____6966)))
in (

let decl = (

let uu____6968 = (FStar_Ident.range_of_lid discriminator_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____6968; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____6970 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____6970) with
| true -> begin
(

let uu____6971 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____6971))
end
| uu____6972 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6975 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____6981 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7022 -> (match (uu____7022) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____7046 = (

let uu____7049 = (

let uu____7050 = (

let uu____7057 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____7057), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7050))
in (pos uu____7049))
in ((uu____7046), (b)))
end
| uu____7062 -> begin
(

let uu____7063 = (

let uu____7066 = (

let uu____7067 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7067))
in (pos uu____7066))
in ((uu____7063), (b)))
end))
end))))
in (

let pat_true = (

let uu____7085 = (

let uu____7088 = (

let uu____7089 = (

let uu____7102 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____7102), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7089))
in (pos uu____7088))
in ((uu____7085), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____7136 = (

let uu____7139 = (

let uu____7140 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7140))
in (pos uu____7139))
in ((uu____7136), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____7152 = (

let uu____7159 = (

let uu____7160 = (

let uu____7183 = (

let uu____7200 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____7201 = (

let uu____7204 = (FStar_Syntax_Util.branch pat_false)
in (uu____7204)::[])
in (uu____7200)::uu____7201))
in ((arg_exp), (uu____7183)))
in FStar_Syntax_Syntax.Tm_match (uu____7160))
in (FStar_Syntax_Syntax.mk uu____7159))
in (uu____7152 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____7227 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7227) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7230 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7239 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____7241 = (

let uu____7246 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7246))
in (

let uu____7247 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in (FStar_Syntax_Util.mk_letbinding uu____7241 uvs lbtyp FStar_Parser_Const.effect_Tot_lid uu____7247 [] FStar_Range.dummyRange)))
in (

let impl = (

let uu____7253 = (

let uu____7254 = (

let uu____7261 = (

let uu____7264 = (

let uu____7265 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____7265 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____7264)::[])
in ((((false), ((lb)::[]))), (uu____7261)))
in FStar_Syntax_Syntax.Sig_let (uu____7254))
in {FStar_Syntax_Syntax.sigel = uu____7253; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____7277 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7277) with
| true -> begin
(

let uu____7278 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____7278))
end
| uu____7279 -> begin
()
end));
(decl)::(impl)::[];
)))))))
end);
))))))))
end)
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst arg_binder))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7330 -> (match (uu____7330) with
| (a, uu____7336) -> begin
(

let uu____7337 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____7337) with
| (field_name, uu____7343) -> begin
(

let field_proj_tm = (

let uu____7345 = (

let uu____7346 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7346))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7345 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____7367 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____7405 -> (match (uu____7405) with
| (x, uu____7413) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____7415 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____7415) with
| (field_name, uu____7423) -> begin
(

let t = (

let uu____7427 = (

let uu____7428 = (

let uu____7431 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____7431))
in (FStar_Syntax_Util.arrow binders uu____7428))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____7427))
in (

let only_decl = (early_prims_inductive || (

let uu____7436 = (

let uu____7437 = (FStar_TypeChecker_Env.current_module env)
in uu____7437.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____7436)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____7453 = (FStar_List.filter (fun uu___69_7457 -> (match (uu___69_7457) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____7458 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____7453)
end
| uu____7459 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___70_7471 -> (match (uu___70_7471) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____7472 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____7478 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = (

let uu____7484 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____7484; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____7486 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7486) with
| true -> begin
(

let uu____7487 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____7487))
end
| uu____7488 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____7491 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____7533 -> (match (uu____7533) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____7557 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____7557), (b)))
end
| uu____7562 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____7573 = (

let uu____7576 = (

let uu____7577 = (

let uu____7584 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____7584), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____7577))
in (pos uu____7576))
in ((uu____7573), (b)))
end
| uu____7589 -> begin
(

let uu____7590 = (

let uu____7593 = (

let uu____7594 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____7594))
in (pos uu____7593))
in ((uu____7590), (b)))
end)
end))
end))))
in (

let pat = (

let uu____7612 = (

let uu____7615 = (

let uu____7616 = (

let uu____7629 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____7629), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____7616))
in (pos uu____7615))
in (

let uu____7638 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____7612), (FStar_Pervasives_Native.None), (uu____7638))))
in (

let body = (

let uu____7654 = (

let uu____7661 = (

let uu____7662 = (

let uu____7685 = (

let uu____7702 = (FStar_Syntax_Util.branch pat)
in (uu____7702)::[])
in ((arg_exp), (uu____7685)))
in FStar_Syntax_Syntax.Tm_match (uu____7662))
in (FStar_Syntax_Syntax.mk uu____7661))
in (uu____7654 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____7728 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____7728) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____7731 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____7737 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____7739 = (

let uu____7744 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7744))
in (

let uu____7745 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____7739; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____7745; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange}))
in (

let impl = (

let uu____7751 = (

let uu____7752 = (

let uu____7759 = (

let uu____7762 = (

let uu____7763 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____7763 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____7762)::[])
in ((((false), ((lb)::[]))), (uu____7759)))
in FStar_Syntax_Syntax.Sig_let (uu____7752))
in {FStar_Syntax_Syntax.sigel = uu____7751; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____7775 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____7775) with
| true -> begin
(

let uu____7776 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____7776))
end
| uu____7777 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____7780 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____7367 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses))))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____7824) when (

let uu____7829 = (FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid)
in (not (uu____7829))) -> begin
(

let uu____7830 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7830) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____7852 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____7852) with
| (formals, uu____7868) -> begin
(

let uu____7885 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____7917 = (

let uu____7918 = (

let uu____7919 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____7919))
in (FStar_Ident.lid_equals typ_lid uu____7918))
in (match (uu____7917) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7938, uvs', tps, typ0, uu____7942, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____7959 -> begin
(failwith "Impossible")
end)
end
| uu____7968 -> begin
FStar_Pervasives_Native.None
end))))
in (match (tps_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8000 = (FStar_Ident.lid_equals typ_lid FStar_Parser_Const.exn_lid)
in (match (uu____8000) with
| true -> begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end
| uu____8011 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____7885) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____8025 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____8025) with
| (indices, uu____8041) -> begin
(

let refine_domain = (

let uu____8059 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___71_8064 -> (match (uu___71_8064) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8065) -> begin
true
end
| uu____8074 -> begin
false
end))))
in (match (uu____8059) with
| true -> begin
false
end
| uu____8075 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___72_8084 -> (match (uu___72_8084) with
| FStar_Syntax_Syntax.RecordConstructor (uu____8087, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____8099 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____8100 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____8100) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| FStar_Pervasives_Native.Some (q) -> begin
q
end)))
in (

let iquals1 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____8109 -> begin
iquals
end)
in (

let fields = (

let uu____8111 = (FStar_Util.first_N n_typars formals)
in (match (uu____8111) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____8176 uu____8177 -> (match (((uu____8176), (uu____8177))) with
| ((x, uu____8195), (x', uu____8197)) -> begin
(

let uu____8206 = (

let uu____8213 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____8213)))
in FStar_Syntax_Syntax.NT (uu____8206))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____8218 -> begin
[]
end))




