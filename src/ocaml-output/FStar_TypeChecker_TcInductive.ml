
open Prims
open FStar_Pervasives

let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.unfold_whnf' ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[]))


let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data) -> begin
(

let env0 = env
in (

let uu____50 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____50) with
| (usubst, uvs1) -> begin
(

let uu____77 = (

let uu____84 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let uu____85 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let uu____86 = (

let uu____87 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps) usubst)
in (FStar_Syntax_Subst.subst uu____87 k))
in ((uu____84), (uu____85), (uu____86)))))
in (match (uu____77) with
| (env1, tps1, k1) -> begin
(

let uu____107 = (FStar_Syntax_Subst.open_term tps1 k1)
in (match (uu____107) with
| (tps2, k2) -> begin
(

let uu____122 = (FStar_TypeChecker_TcTerm.tc_binders env1 tps2)
in (match (uu____122) with
| (tps3, env_tps, guard_params, us) -> begin
(

let uu____143 = (

let uu____162 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env_tps k2)
in (match (uu____162) with
| (k3, uu____188, g) -> begin
(

let k4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta))::[]) env_tps k3)
in (

let uu____191 = (FStar_Syntax_Util.arrow_formals k4)
in (

let uu____206 = (

let uu____207 = (FStar_TypeChecker_Env.conj_guard guard_params g)
in (FStar_TypeChecker_Rel.discharge_guard env_tps uu____207))
in ((uu____191), (uu____206)))))
end))
in (match (uu____143) with
| ((indices, t), guard) -> begin
(

let k3 = (

let uu____270 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices uu____270))
in (

let uu____273 = (FStar_Syntax_Util.type_u ())
in (match (uu____273) with
| (t_type, u) -> begin
(

let valid_type = (((FStar_Syntax_Util.is_eqtype_no_unrefine t) && (

let uu____291 = (FStar_All.pipe_right s.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Unopteq))
in (not (uu____291)))) || (FStar_TypeChecker_Rel.teq_nosmt_force env1 t t_type))
in ((match ((not (valid_type))) with
| true -> begin
(

let uu____298 = (

let uu____304 = (

let uu____306 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____308 = (FStar_Ident.string_of_lid tc)
in (FStar_Util.format2 "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier" uu____306 uu____308)))
in ((FStar_Errors.Error_InductiveAnnotNotAType), (uu____304)))
in (FStar_Errors.raise_error uu____298 s.FStar_Syntax_Syntax.sigrng))
end
| uu____312 -> begin
()
end);
(

let usubst1 = (FStar_Syntax_Subst.univ_var_closing uvs1)
in (

let guard1 = (FStar_TypeChecker_Util.close_guard_implicits env1 tps3 guard)
in (

let t_tc = (

let uu____321 = (

let uu____330 = (FStar_All.pipe_right tps3 (FStar_Syntax_Subst.subst_binders usubst1))
in (

let uu____347 = (

let uu____356 = (

let uu____369 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps3) usubst1)
in (FStar_Syntax_Subst.subst_binders uu____369))
in (FStar_All.pipe_right indices uu____356))
in (FStar_List.append uu____330 uu____347)))
in (

let uu____392 = (

let uu____395 = (

let uu____396 = (

let uu____401 = (FStar_Syntax_Subst.shift_subst ((FStar_List.length tps3) + (FStar_List.length indices)) usubst1)
in (FStar_Syntax_Subst.subst uu____401))
in (FStar_All.pipe_right t uu____396))
in (FStar_Syntax_Syntax.mk_Total uu____395))
in (FStar_Syntax_Util.arrow uu____321 uu____392)))
in (

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let k4 = (FStar_Syntax_Subst.close tps4 k3)
in (

let uu____418 = (

let uu____423 = (FStar_Syntax_Subst.subst_binders usubst1 tps4)
in (

let uu____424 = (

let uu____425 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps4) usubst1)
in (FStar_Syntax_Subst.subst uu____425 k4))
in ((uu____423), (uu____424))))
in (match (uu____418) with
| (tps5, k5) -> begin
(

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____445 = (FStar_TypeChecker_Env.push_let_binding env0 (FStar_Util.Inr (fv_tc)) ((uvs1), (t_tc)))
in ((uu____445), ((

let uu___61_451 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps5), (k5), (mutuals), (data))); FStar_Syntax_Syntax.sigrng = uu___61_451.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___61_451.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___61_451.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___61_451.FStar_Syntax_Syntax.sigattrs})), (u), (guard1))))
end)))))));
))
end)))
end))
end))
end))
end))
end)))
end
| uu____456 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, _mutual_tcs) -> begin
(

let uu____520 = (FStar_Syntax_Subst.univ_var_opening _uvs)
in (match (uu____520) with
| (usubst, _uvs1) -> begin
(

let uu____543 = (

let uu____548 = (FStar_TypeChecker_Env.push_univ_vars env _uvs1)
in (

let uu____549 = (FStar_Syntax_Subst.subst usubst t)
in ((uu____548), (uu____549))))
in (match (uu____543) with
| (env1, t1) -> begin
(

let uu____556 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____595 -> (match (uu____595) with
| (se1, u_tc) -> begin
(

let uu____610 = (

let uu____612 = (

let uu____613 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____613))
in (FStar_Ident.lid_equals tc_lid uu____612))
in (match (uu____610) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____633, uu____634, tps, uu____636, uu____637, uu____638) -> begin
(

let tps1 = (

let uu____648 = (FStar_All.pipe_right tps (FStar_Syntax_Subst.subst_binders usubst))
in (FStar_All.pipe_right uu____648 (FStar_List.map (fun uu____688 -> (match (uu____688) with
| (x, uu____702) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____710 = (

let uu____717 = (FStar_TypeChecker_Env.push_binders env1 tps2)
in ((uu____717), (tps2), (u_tc)))
in FStar_Pervasives_Native.Some (uu____710))))
end
| uu____724 -> begin
(failwith "Impossible")
end)
end
| uu____734 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (tps_u_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____767 = (FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid)
in (match (uu____767) with
| true -> begin
((env1), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____782 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____556) with
| (env2, tps, u_tc) -> begin
(

let uu____799 = (

let t2 = (FStar_TypeChecker_Normalize.normalize (FStar_List.append FStar_TypeChecker_Normalize.whnf_steps ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[])) env2 t1)
in (

let uu____815 = (

let uu____816 = (FStar_Syntax_Subst.compress t2)
in uu____816.FStar_Syntax_Syntax.n)
in (match (uu____815) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____855 = (FStar_Util.first_N ntps bs)
in (match (uu____855) with
| (uu____896, bs') -> begin
(

let t3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____967 -> (match (uu____967) with
| (x, uu____976) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____983 = (FStar_Syntax_Subst.subst subst1 t3)
in (FStar_Syntax_Util.arrow_formals uu____983))))
end))
end
| uu____984 -> begin
(([]), (t2))
end)))
in (match (uu____799) with
| (arguments, result) -> begin
((

let uu____1028 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____1028) with
| true -> begin
(

let uu____1031 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____1033 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____1036 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____1031 uu____1033 uu____1036))))
end
| uu____1039 -> begin
()
end));
(

let uu____1041 = (FStar_TypeChecker_TcTerm.tc_tparams env2 arguments)
in (match (uu____1041) with
| (arguments1, env', us) -> begin
(

let type_u_tc = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u_tc)) FStar_Pervasives_Native.None result.FStar_Syntax_Syntax.pos)
in (

let env'1 = (FStar_TypeChecker_Env.set_expected_typ env' type_u_tc)
in (

let uu____1059 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env'1 result)
in (match (uu____1059) with
| (result1, res_lcomp) -> begin
(

let uu____1070 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____1070) with
| (head1, args) -> begin
(

let p_args = (

let uu____1128 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_Pervasives_Native.fst uu____1128))
in ((FStar_List.iter2 (fun uu____1210 uu____1211 -> (match (((uu____1210), (uu____1211))) with
| ((bv, uu____1241), (t2, uu____1243)) -> begin
(

let uu____1270 = (

let uu____1271 = (FStar_Syntax_Subst.compress t2)
in uu____1271.FStar_Syntax_Syntax.n)
in (match (uu____1270) with
| FStar_Syntax_Syntax.Tm_name (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
()
end
| uu____1275 -> begin
(

let uu____1276 = (

let uu____1282 = (

let uu____1284 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____1286 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "This parameter is not constant: expected %s, got %s" uu____1284 uu____1286)))
in ((FStar_Errors.Error_BadInductiveParam), (uu____1282)))
in (FStar_Errors.raise_error uu____1276 t2.FStar_Syntax_Syntax.pos))
end))
end)) tps p_args);
(

let ty = (

let uu____1291 = (unfold_whnf env2 res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_right uu____1291 FStar_Syntax_Util.unrefine))
in ((

let uu____1293 = (

let uu____1294 = (FStar_Syntax_Subst.compress ty)
in uu____1294.FStar_Syntax_Syntax.n)
in (match (uu____1293) with
| FStar_Syntax_Syntax.Tm_type (uu____1297) -> begin
()
end
| uu____1298 -> begin
(

let uu____1299 = (

let uu____1305 = (

let uu____1307 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____1309 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____1307 uu____1309)))
in ((FStar_Errors.Fatal_WrongResultTypeAfterConstrutor), (uu____1305)))
in (FStar_Errors.raise_error uu____1299 se.FStar_Syntax_Syntax.sigrng))
end));
(

let g_uvs = (

let uu____1314 = (

let uu____1315 = (FStar_Syntax_Subst.compress head1)
in uu____1315.FStar_Syntax_Syntax.n)
in (match (uu____1314) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1319; FStar_Syntax_Syntax.vars = uu____1320}, tuvs) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
(match ((Prims.op_Equality (FStar_List.length _uvs1) (FStar_List.length tuvs))) with
| true -> begin
(FStar_List.fold_left2 (fun g u1 u2 -> (

let uu____1334 = (

let uu____1335 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____1336 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u2))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_TypeChecker_Rel.teq env'1 uu____1335 uu____1336)))
in (FStar_TypeChecker_Env.conj_guard g uu____1334))) FStar_TypeChecker_Env.trivial_guard tuvs _uvs1)
end
| uu____1337 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedConstructorType), ("Length of annotated universes does not match inferred universes")) se.FStar_Syntax_Syntax.sigrng)
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
FStar_TypeChecker_Env.trivial_guard
end
| uu____1342 -> begin
(

let uu____1343 = (

let uu____1349 = (

let uu____1351 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____1353 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____1351 uu____1353)))
in ((FStar_Errors.Fatal_UnexpectedConstructorType), (uu____1349)))
in (FStar_Errors.raise_error uu____1343 se.FStar_Syntax_Syntax.sigrng))
end))
in (

let g = (FStar_List.fold_left2 (fun g uu____1371 u_x -> (match (uu____1371) with
| (x, uu____1380) -> begin
(

let uu____1385 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Env.conj_guard g uu____1385))
end)) g_uvs arguments1 us)
in (

let t2 = (

let uu____1389 = (

let uu____1398 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____1438 -> (match (uu____1438) with
| (x, uu____1452) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____1398 arguments1))
in (

let uu____1466 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____1389 uu____1466)))
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars _uvs1 t2)
in (((

let uu___183_1471 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), (_uvs1), (t3), (tc_lid), (ntps), ([]))); FStar_Syntax_Syntax.sigrng = uu___183_1471.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___183_1471.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___183_1471.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___183_1471.FStar_Syntax_Syntax.sigattrs})), (g))))));
));
))
end))
end))))
end));
)
end))
end))
end))
end))
end
| uu____1475 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map FStar_Pervasives_Native.snd tcs)
in (

let g1 = (

let uu___191_1542 = g
in {FStar_TypeChecker_Env.guard_f = uu___191_1542.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___191_1542.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((FStar_Pervasives_Native.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___191_1542.FStar_TypeChecker_Env.implicits})
in ((

let uu____1552 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1552) with
| true -> begin
(

let uu____1557 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____1557))
end
| uu____1560 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____1600 -> (match (uu____1600) with
| (se, uu____1606) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1607, uu____1608, tps, k, uu____1611, uu____1612) -> begin
(

let uu____1621 = (

let uu____1622 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____1622))
in (FStar_Syntax_Syntax.null_binder uu____1621))
end
| uu____1627 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1656, uu____1657, t, uu____1659, uu____1660, uu____1661) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____1668 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____1673 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____1673))
in ((

let uu____1683 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1683) with
| true -> begin
(

let uu____1688 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____1688))
end
| uu____1691 -> begin
()
end));
(

let uu____1693 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____1693) with
| (uvs, t1) -> begin
((

let uu____1713 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1713) with
| true -> begin
(

let uu____1718 = (

let uu____1720 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____1720 (FStar_String.concat ", ")))
in (

let uu____1737 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____1718 uu____1737)))
end
| uu____1740 -> begin
()
end));
(

let uu____1742 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____1742) with
| (uvs1, t2) -> begin
(

let uu____1757 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____1757) with
| (args, uu____1781) -> begin
(

let uu____1802 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____1802) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____1907 uu____1908 -> (match (((uu____1907), (uu____1908))) with
| ((x, uu____1930), (se, uu____1932)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1948, tps, uu____1950, mutuals, datas1) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____1962 = (

let uu____1967 = (

let uu____1968 = (FStar_Syntax_Subst.compress ty)
in uu____1968.FStar_Syntax_Syntax.n)
in (match (uu____1967) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____1997 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____1997) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____2075 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos)
end)
in ((tps1), (t3)))
end))
end
| uu____2094 -> begin
(([]), (ty))
end))
in (match (uu____1962) with
| (tps1, t3) -> begin
(

let uu___268_2103 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1))); FStar_Syntax_Syntax.sigrng = uu___268_2103.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___268_2103.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___268_2103.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___268_2103.FStar_Syntax_Syntax.sigattrs})
end)))
end
| uu____2108 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____2115 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _2119 -> FStar_Syntax_Syntax.U_name (_2119))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___0_2138 -> (match (uu___0_2138) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2144, uu____2145, uu____2146, uu____2147, uu____2148); FStar_Syntax_Syntax.sigrng = uu____2149; FStar_Syntax_Syntax.sigquals = uu____2150; FStar_Syntax_Syntax.sigmeta = uu____2151; FStar_Syntax_Syntax.sigattrs = uu____2152} -> begin
((tc), (uvs_universes))
end
| uu____2165 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____2189 d -> (match (uu____2189) with
| (t3, uu____2198) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____2204, uu____2205, tc, ntps, mutuals) -> begin
(

let ty = (

let uu____2216 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2216 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___304_2217 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___304_2217.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___304_2217.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___304_2217.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___304_2217.FStar_Syntax_Syntax.sigattrs}))
end
| uu____2221 -> begin
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

let uu____2240 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____2240) with
| true -> begin
(FStar_Util.print_string (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n")))
end
| uu____2247 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____2262 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____2262)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____2279 = (

let uu____2280 = (FStar_Syntax_Subst.compress t)
in uu____2280.FStar_Syntax_Syntax.n)
in (match (uu____2279) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____2299 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____2305 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____2342 = (FStar_ST.op_Bang unfolded)
in (FStar_List.existsML (fun uu____2391 -> (match (uu____2391) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____2435 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (FStar_Pervasives_Native.fst uu____2435))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt_force env (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst a')))) true args l)))
end)) uu____2342)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____2640 = (

let uu____2642 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.op_Hat "Checking strict positivity in type: " uu____2642))
in (debug_log env uu____2640));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____2647 = (

let uu____2649 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.op_Hat "Checking strict positivity in type, after normalization: " uu____2649))
in (debug_log env uu____2647));
((

let uu____2654 = (ty_occurs_in ty_lid btype1)
in (not (uu____2654))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____2667 = (

let uu____2668 = (FStar_Syntax_Subst.compress btype1)
in uu____2668.FStar_Syntax_Syntax.n)
in (match (uu____2667) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____2698 = (try_get_fv t)
in (match (uu____2698) with
| (fv, us) -> begin
(

let uu____2706 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)
in (match (uu____2706) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____2722 -> (match (uu____2722) with
| (t1, uu____2731) -> begin
(

let uu____2736 = (ty_occurs_in ty_lid t1)
in (not (uu____2736)))
end)) args);
)
end
| uu____2738 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let check_comp1 = (

let c1 = (

let uu____2771 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____2771 FStar_Syntax_Syntax.mk_Comp))
in ((FStar_Syntax_Util.is_pure_or_ghost_comp c1) || (

let uu____2775 = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c1))
in (FStar_All.pipe_right uu____2775 (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.TotalEffect)))))))
in (match ((not (check_comp1))) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____2788 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____2802 -> (match (uu____2802) with
| (b, uu____2811) -> begin
(

let uu____2816 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____2816)))
end)) sbs) && (

let uu____2822 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____2822) with
| (uu____2828, return_type) -> begin
(

let uu____2830 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____2830))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2831) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____2835) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2840) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____2848) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____2855, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____2914 -> (match (uu____2914) with
| (p, uu____2927, t) -> begin
(

let bs = (

let uu____2946 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____2946))
in (

let uu____2955 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2955) with
| (bs1, t1) -> begin
(

let uu____2963 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____2963))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____2965, uu____2966) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____3009 -> begin
((

let uu____3011 = (

let uu____3013 = (

let uu____3015 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____3017 = (

let uu____3019 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.op_Hat " and term: " uu____3019))
in (Prims.op_Hat uu____3015 uu____3017)))
in (Prims.op_Hat "Checking strict positivity, unexpected tag: " uu____3013))
in (debug_log env uu____3011));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____3032 = (

let uu____3034 = (

let uu____3036 = (

let uu____3038 = (FStar_Syntax_Print.args_to_string args)
in (Prims.op_Hat " applied to arguments: " uu____3038))
in (Prims.op_Hat ilid.FStar_Ident.str uu____3036))
in (Prims.op_Hat "Checking nested positivity in the inductive " uu____3034))
in (debug_log env uu____3032));
(

let uu____3042 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____3042) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
(

let uu____3061 = (

let uu____3063 = (FStar_Syntax_Syntax.lid_as_fv ilid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Env.fv_has_attr env uu____3063 FStar_Parser_Const.assume_strictly_positive_attr_lid))
in (match (uu____3061) with
| true -> begin
((

let uu____3067 = (

let uu____3069 = (FStar_Ident.string_of_lid ilid)
in (FStar_Util.format1 "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true" uu____3069))
in (debug_log env uu____3067));
true;
)
end
| uu____3073 -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end))
end
| uu____3078 -> begin
(

let uu____3080 = (already_unfolded ilid args unfolded env)
in (match (uu____3080) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____3087 -> begin
(

let num_ibs = (

let uu____3091 = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in (FStar_Option.get uu____3091))
in ((

let uu____3097 = (

let uu____3099 = (

let uu____3101 = (FStar_Util.string_of_int num_ibs)
in (Prims.op_Hat uu____3101 ", also adding to the memo table"))
in (Prims.op_Hat "Checking nested positivity, number of type parameters is " uu____3099))
in (debug_log env uu____3097));
(

let uu____3106 = (

let uu____3107 = (FStar_ST.op_Bang unfolded)
in (

let uu____3133 = (

let uu____3140 = (

let uu____3145 = (

let uu____3146 = (FStar_List.splitAt num_ibs args)
in (FStar_Pervasives_Native.fst uu____3146))
in ((ilid), (uu____3145)))
in (uu____3140)::[])
in (FStar_List.append uu____3107 uu____3133)))
in (FStar_ST.op_Colon_Equals unfolded uu____3106));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.op_Hat "Checking nested positivity in data constructor " (Prims.op_Hat dlid.FStar_Ident.str (Prims.op_Hat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____3245 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3245) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3268 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____3272 = (

let uu____3274 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.op_Hat "Checking nested positivity in the data constructor type: " uu____3274))
in (debug_log env uu____3272));
(

let uu____3277 = (

let uu____3278 = (FStar_Syntax_Subst.compress dt1)
in uu____3278.FStar_Syntax_Syntax.n)
in (match (uu____3277) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____3306 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____3306) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____3370 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____3370 dbs1))
in (

let c1 = (

let uu____3374 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____3374 c))
in (

let uu____3377 = (FStar_List.splitAt num_ibs args)
in (match (uu____3377) with
| (args1, uu____3412) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst ib)), ((FStar_Pervasives_Native.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____3504 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____3504 c1))
in ((

let uu____3514 = (

let uu____3516 = (

let uu____3518 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____3521 = (

let uu____3523 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.op_Hat ", and c: " uu____3523))
in (Prims.op_Hat uu____3518 uu____3521)))
in (Prims.op_Hat "Checking nested positivity in the unfolded data constructor binders as: " uu____3516))
in (debug_log env uu____3514));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____3537 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____3540 = (

let uu____3541 = (FStar_Syntax_Subst.compress dt1)
in uu____3541.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____3540 ilid num_ibs unfolded env));
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

let uu____3580 = (try_get_fv t1)
in (match (uu____3580) with
| (fv, uu____3587) -> begin
(

let uu____3588 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)
in (match (uu____3588) with
| true -> begin
true
end
| uu____3593 -> begin
(failwith "Impossible, expected the type to be ilid")
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____3620 = (

let uu____3622 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.op_Hat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____3622))
in (debug_log env uu____3620));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____3627 = (FStar_List.fold_left (fun uu____3648 b -> (match (uu____3648) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3677 -> begin
(

let uu____3679 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3683 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3679), (uu____3683))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____3627) with
| (b, uu____3701) -> begin
b
end)));
)
end
| uu____3704 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____3740 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3740) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3763 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____3766 = (

let uu____3768 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.op_Hat "Checking data constructor type: " uu____3768))
in (debug_log env uu____3766));
(

let uu____3771 = (

let uu____3772 = (FStar_Syntax_Subst.compress dt)
in uu____3772.FStar_Syntax_Syntax.n)
in (match (uu____3771) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3776) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3781) -> begin
(

let dbs1 = (

let uu____3811 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (FStar_Pervasives_Native.snd uu____3811))
in (

let dbs2 = (

let uu____3861 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____3861 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____3866 = (

let uu____3868 = (

let uu____3870 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.op_Hat uu____3870 " binders"))
in (Prims.op_Hat "Data constructor type is an arrow type, so checking strict positivity in " uu____3868))
in (debug_log env uu____3866));
(

let uu____3880 = (FStar_List.fold_left (fun uu____3901 b -> (match (uu____3901) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3930 -> begin
(

let uu____3932 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3936 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3932), (uu____3936))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____3880) with
| (b, uu____3954) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____3957, uu____3958) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, univs1) -> begin
((debug_log env "Data constructor type is a Tm_uinst, so recursing in the base type");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____3994 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____4017 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____4033, uu____4034, uu____4035) -> begin
((lid), (us), (bs))
end
| uu____4044 -> begin
(failwith "Impossible!")
end)
in (match (uu____4017) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____4056 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____4056) with
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

let uu____4080 = (

let uu____4083 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (FStar_Pervasives_Native.snd uu____4083))
in (FStar_List.for_all (fun d -> (

let uu____4097 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____4097 unfolded_inductives env2))) uu____4080))))))
end))
end))))


let check_exn_positivity : FStar_Ident.lid  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun data_ctor_lid env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] [] unfolded_inductives env)))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4132, uu____4133, t, uu____4135, uu____4136, uu____4137) -> begin
t
end
| uu____4144 -> begin
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

let uu____4161 = (

let uu____4163 = (FStar_String.substring str (len - haseq_suffix_len) haseq_suffix_len)
in (FStar_String.compare uu____4163 haseq_suffix))
in (Prims.op_Equality uu____4161 (Prims.parse_int "0"))))))))


let get_haseq_axiom_lid : FStar_Ident.lid  ->  FStar_Ident.lid = (fun lid -> (

let uu____4173 = (

let uu____4176 = (

let uu____4179 = (FStar_Ident.id_of_text (Prims.op_Hat lid.FStar_Ident.ident.FStar_Ident.idText haseq_suffix))
in (uu____4179)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____4176))
in (FStar_Ident.lid_of_ids uu____4173)))


let get_optimized_haseq_axiom : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_names  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun en ty usubst us -> (

let uu____4225 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4239, bs, t, uu____4242, uu____4243) -> begin
((lid), (bs), (t))
end
| uu____4252 -> begin
(failwith "Impossible!")
end)
in (match (uu____4225) with
| (lid, bs, t) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____4275 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____4275 t))
in (

let uu____4284 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____4284) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____4302 = (

let uu____4303 = (FStar_Syntax_Subst.compress t2)
in uu____4303.FStar_Syntax_Syntax.n)
in (match (uu____4302) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4307) -> begin
ibs
end
| uu____4328 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____4337 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____4338 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4337 uu____4338)))
in (

let ind1 = (

let uu____4344 = (

let uu____4349 = (FStar_List.map (fun uu____4366 -> (match (uu____4366) with
| (bv, aq) -> begin
(

let uu____4385 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4385), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4349))
in (uu____4344 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____4391 = (

let uu____4396 = (FStar_List.map (fun uu____4413 -> (match (uu____4413) with
| (bv, aq) -> begin
(

let uu____4432 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4432), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4396))
in (uu____4391 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____4438 = (

let uu____4443 = (

let uu____4444 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____4444)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4443))
in (uu____4438 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____4493 = (

let uu____4494 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____4494))
in (FStar_TypeChecker_Rel.subtype_nosmt_force en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____4493))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____4507 = (

let uu____4510 = (

let uu____4515 = (

let uu____4516 = (

let uu____4525 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____4525))
in (uu____4516)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4515))
in (uu____4510 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____4507))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___638_4548 = fml
in (

let uu____4549 = (

let uu____4550 = (

let uu____4557 = (

let uu____4558 = (

let uu____4579 = (FStar_Syntax_Syntax.binders_to_names ibs1)
in (

let uu____4584 = (

let uu____4597 = (

let uu____4608 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____4608)::[])
in (uu____4597)::[])
in ((uu____4579), (uu____4584))))
in FStar_Syntax_Syntax.Meta_pattern (uu____4558))
in ((fml), (uu____4557)))
in FStar_Syntax_Syntax.Tm_meta (uu____4550))
in {FStar_Syntax_Syntax.n = uu____4549; FStar_Syntax_Syntax.pos = uu___638_4548.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___638_4548.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____4677 = (

let uu____4682 = (

let uu____4683 = (

let uu____4692 = (

let uu____4693 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4693 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4692))
in (uu____4683)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4682))
in (uu____4677 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____4746 = (

let uu____4751 = (

let uu____4752 = (

let uu____4761 = (

let uu____4762 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4762 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4761))
in (uu____4752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4751))
in (uu____4746 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
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

let uu____4837 = (

let uu____4838 = (FStar_Syntax_Subst.compress dt1)
in uu____4838.FStar_Syntax_Syntax.n)
in (match (uu____4837) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4842) -> begin
(

let dbs1 = (

let uu____4872 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____4872))
in (

let dbs2 = (

let uu____4922 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____4922 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____4937 = (

let uu____4942 = (

let uu____4943 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____4943)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4942))
in (uu____4937 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sort_range = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____4974 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____4974 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____4982 = (

let uu____4987 = (

let uu____4988 = (

let uu____4997 = (

let uu____4998 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4998 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4997))
in (uu____4988)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4987))
in (uu____4982 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____5045 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty : FStar_Syntax_Syntax.sigelts  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.sigelt  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun all_datas_in_the_bundle usubst us acc ty -> (

let lid = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5136, uu____5137, uu____5138, uu____5139, uu____5140) -> begin
lid
end
| uu____5149 -> begin
(failwith "Impossible!")
end)
in (

let uu____5151 = acc
in (match (uu____5151) with
| (uu____5188, en, uu____5190, uu____5191) -> begin
(

let uu____5212 = (get_optimized_haseq_axiom en ty usubst us)
in (match (uu____5212) with
| (axiom_lid, fml, bs, ibs, haseq_bs) -> begin
(

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____5249 = acc
in (match (uu____5249) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5324, uu____5325, uu____5326, t_lid, uu____5328, uu____5329) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____5336 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____5351 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc1 uu____5351))) FStar_Syntax_Util.t_true t_datas)
in (

let uu____5354 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____5357 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env2), (uu____5354), (uu____5357))))))))
end)))
end))
end))))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let uu____5415 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5425, us, uu____5427, t, uu____5429, uu____5430) -> begin
((us), (t))
end
| uu____5439 -> begin
(failwith "Impossible!")
end))
in (match (uu____5415) with
| (us, t) -> begin
(

let uu____5449 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5449) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____5475 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____5475) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (

let uu____5553 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____5553) with
| (uu____5568, t1) -> begin
(

let uu____5590 = (FStar_Syntax_Util.is_eqtype_no_unrefine t1)
in (match (uu____5590) with
| true -> begin
cond
end
| uu____5593 -> begin
(FStar_Syntax_Util.mk_imp guard cond)
end))
end))
in (

let uu____5595 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____5595) with
| (phi1, uu____5603) -> begin
((

let uu____5605 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____5605) with
| true -> begin
(

let uu____5608 = (FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____5608))
end
| uu____5609 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____5626 -> (match (uu____5626) with
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
end))
end)))


let unoptimized_haseq_data : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun usubst bs haseq_ind mutuals acc data -> (

let rec is_mutual = (fun t -> (

let uu____5698 = (

let uu____5699 = (FStar_Syntax_Subst.compress t)
in uu____5699.FStar_Syntax_Syntax.n)
in (match (uu____5698) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____5707) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____5744 = (is_mutual t')
in (match (uu____5744) with
| true -> begin
true
end
| uu____5749 -> begin
(

let uu____5751 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (exists_mutual uu____5751))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____5771) -> begin
(is_mutual t')
end
| uu____5776 -> begin
false
end)))
and exists_mutual = (fun uu___1_5778 -> (match (uu___1_5778) with
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

let uu____5799 = (

let uu____5800 = (FStar_Syntax_Subst.compress dt1)
in uu____5800.FStar_Syntax_Syntax.n)
in (match (uu____5799) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5806) -> begin
(

let dbs1 = (

let uu____5836 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____5836))
in (

let dbs2 = (

let uu____5886 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5886 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____5906 = (

let uu____5911 = (

let uu____5912 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____5912)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5911))
in (uu____5906 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____5942 = (is_mutual sort)
in (match (uu____5942) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____5947 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____5955 = (

let uu____5960 = (

let uu____5961 = (

let uu____5970 = (

let uu____5971 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____5971 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____5970))
in (uu____5961)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5960))
in (uu____5955 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____6018 -> begin
acc
end))))))


let unoptimized_haseq_ty : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____6068 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6090, bs, t, uu____6093, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____6105 -> begin
(failwith "Impossible!")
end)
in (match (uu____6068) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____6129 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____6129 t))
in (

let uu____6138 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____6138) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____6148 = (

let uu____6149 = (FStar_Syntax_Subst.compress t2)
in uu____6149.FStar_Syntax_Syntax.n)
in (match (uu____6148) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____6153) -> begin
ibs
end
| uu____6174 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____6183 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____6184 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6183 uu____6184)))
in (

let ind1 = (

let uu____6190 = (

let uu____6195 = (FStar_List.map (fun uu____6212 -> (match (uu____6212) with
| (bv, aq) -> begin
(

let uu____6231 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____6231), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____6195))
in (uu____6190 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____6237 = (

let uu____6242 = (FStar_List.map (fun uu____6259 -> (match (uu____6259) with
| (bv, aq) -> begin
(

let uu____6278 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____6278), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6242))
in (uu____6237 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____6284 = (

let uu____6289 = (

let uu____6290 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____6290)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____6289))
in (uu____6284 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____6327, uu____6328, uu____6329, t_lid, uu____6331, uu____6332) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____6339 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___875_6351 = fml
in (

let uu____6352 = (

let uu____6353 = (

let uu____6360 = (

let uu____6361 = (

let uu____6382 = (FStar_Syntax_Syntax.binders_to_names ibs1)
in (

let uu____6387 = (

let uu____6400 = (

let uu____6411 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____6411)::[])
in (uu____6400)::[])
in ((uu____6382), (uu____6387))))
in FStar_Syntax_Syntax.Meta_pattern (uu____6361))
in ((fml), (uu____6360)))
in FStar_Syntax_Syntax.Tm_meta (uu____6353))
in {FStar_Syntax_Syntax.n = uu____6352; FStar_Syntax_Syntax.pos = uu___875_6351.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___875_6351.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____6480 = (

let uu____6485 = (

let uu____6486 = (

let uu____6495 = (

let uu____6496 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____6496 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____6495))
in (uu____6486)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____6485))
in (uu____6480 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____6549 = (

let uu____6554 = (

let uu____6555 = (

let uu____6564 = (

let uu____6565 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____6565 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____6564))
in (uu____6555)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____6554))
in (uu____6549 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6657, uu____6658, uu____6659, uu____6660, uu____6661) -> begin
lid
end
| uu____6670 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____6672 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____6684, uu____6685, uu____6686, uu____6687) -> begin
((lid), (us))
end
| uu____6696 -> begin
(failwith "Impossible!")
end))
in (match (uu____6672) with
| (lid, us) -> begin
(

let uu____6706 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____6706) with
| (usubst, us1) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us1) FStar_Syntax_Util.t_true tcs)
in (

let se = (

let uu____6733 = (

let uu____6734 = (

let uu____6741 = (get_haseq_axiom_lid lid)
in ((uu____6741), (us1), (fml)))
in FStar_Syntax_Syntax.Sig_assume (uu____6734))
in {FStar_Syntax_Syntax.sigel = uu____6733; FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (se)::[]))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____6795 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___2_6820 -> (match (uu___2_6820) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6822); FStar_Syntax_Syntax.sigrng = uu____6823; FStar_Syntax_Syntax.sigquals = uu____6824; FStar_Syntax_Syntax.sigmeta = uu____6825; FStar_Syntax_Syntax.sigattrs = uu____6826} -> begin
true
end
| uu____6848 -> begin
false
end))))
in (match (uu____6795) with
| (tys, datas) -> begin
((

let uu____6871 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___3_6882 -> (match (uu___3_6882) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6884); FStar_Syntax_Syntax.sigrng = uu____6885; FStar_Syntax_Syntax.sigquals = uu____6886; FStar_Syntax_Syntax.sigmeta = uu____6887; FStar_Syntax_Syntax.sigattrs = uu____6888} -> begin
false
end
| uu____6909 -> begin
true
end))))
in (match (uu____6871) with
| true -> begin
(

let uu____6912 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType), ("Mutually defined type contains a non-inductive element")) uu____6912))
end
| uu____6915 -> begin
()
end));
(

let univs1 = (match ((Prims.op_Equality (FStar_List.length tys) (Prims.parse_int "0"))) with
| true -> begin
[]
end
| uu____6925 -> begin
(

let uu____6927 = (

let uu____6928 = (FStar_List.hd tys)
in uu____6928.FStar_Syntax_Syntax.sigel)
in (match (uu____6927) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6931, uvs, uu____6933, uu____6934, uu____6935, uu____6936) -> begin
uvs
end
| uu____6945 -> begin
(failwith "Impossible, can\'t happen!")
end))
end)
in (

let env0 = env
in (

let uu____6950 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
((env), (tys), (datas))
end
| uu____6978 -> begin
(

let uu____6980 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____6980) with
| (subst1, univs2) -> begin
(

let tys1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____7018, bs, t, l1, l2) -> begin
(

let uu____7031 = (

let uu____7048 = (FStar_Syntax_Subst.subst_binders subst1 bs)
in (

let uu____7049 = (

let uu____7050 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) subst1)
in (FStar_Syntax_Subst.subst uu____7050 t))
in ((lid), (univs2), (uu____7048), (uu____7049), (l1), (l2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____7031))
end
| uu____7063 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___971_7065 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___971_7065.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___971_7065.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___971_7065.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___971_7065.FStar_Syntax_Syntax.sigattrs}))) tys)
in (

let datas1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____7075, t, lid_t, x, l) -> begin
(

let uu____7086 = (

let uu____7102 = (FStar_Syntax_Subst.subst subst1 t)
in ((lid), (univs2), (uu____7102), (lid_t), (x), (l)))
in FStar_Syntax_Syntax.Sig_datacon (uu____7086))
end
| uu____7106 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___985_7108 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___985_7108.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___985_7108.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___985_7108.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___985_7108.FStar_Syntax_Syntax.sigattrs}))) datas)
in (

let uu____7109 = (FStar_TypeChecker_Env.push_univ_vars env univs2)
in ((uu____7109), (tys1), (datas1)))))
end))
end)
in (match (uu____6950) with
| (env1, tys1, datas1) -> begin
(

let uu____7135 = (FStar_List.fold_right (fun tc uu____7174 -> (match (uu____7174) with
| (env2, all_tcs, g) -> begin
(

let uu____7214 = (tc_tycon env2 tc)
in (match (uu____7214) with
| (env3, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____7241 = (FStar_TypeChecker_Env.debug env3 FStar_Options.Low)
in (match (uu____7241) with
| true -> begin
(

let uu____7244 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____7244))
end
| uu____7247 -> begin
()
end));
(

let uu____7249 = (

let uu____7250 = (FStar_TypeChecker_Env.conj_guard guard g')
in (FStar_TypeChecker_Env.conj_guard g uu____7250))
in ((env3), ((((tc1), (tc_u)))::all_tcs), (uu____7249)));
))
end))
end)) tys1 ((env1), ([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____7135) with
| (env2, tcs, g) -> begin
(

let uu____7296 = (FStar_List.fold_right (fun se uu____7318 -> (match (uu____7318) with
| (datas2, g1) -> begin
(

let uu____7337 = (

let uu____7342 = (tc_data env2 tcs)
in (uu____7342 se))
in (match (uu____7337) with
| (data, g') -> begin
(

let uu____7359 = (FStar_TypeChecker_Env.conj_guard g1 g')
in (((data)::datas2), (uu____7359)))
end))
end)) datas1 (([]), (g)))
in (match (uu____7296) with
| (datas2, g1) -> begin
(

let uu____7380 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
(generalize_and_inst_within env1 g1 tcs datas2)
end
| uu____7400 -> begin
(

let uu____7402 = (FStar_List.map FStar_Pervasives_Native.fst tcs)
in ((uu____7402), (datas2)))
end)
in (match (uu____7380) with
| (tcs1, datas3) -> begin
(

let sig_bndle = (

let uu____7434 = (FStar_TypeChecker_Env.get_range env0)
in (

let uu____7435 = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) ses)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas3)), (lids))); FStar_Syntax_Syntax.sigrng = uu____7434; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = uu____7435}))
in ((FStar_All.pipe_right tcs1 (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs2, binders, typ, uu____7461, uu____7462) -> begin
(

let fail1 = (fun expected inferred -> (

let uu____7482 = (

let uu____7488 = (

let uu____7490 = (FStar_Syntax_Print.tscheme_to_string expected)
in (

let uu____7492 = (FStar_Syntax_Print.tscheme_to_string inferred)
in (FStar_Util.format2 "Expected an inductive with type %s; got %s" uu____7490 uu____7492)))
in ((FStar_Errors.Fatal_UnexpectedInductivetype), (uu____7488)))
in (FStar_Errors.raise_error uu____7482 se.FStar_Syntax_Syntax.sigrng)))
in (

let uu____7496 = (FStar_TypeChecker_Env.try_lookup_val_decl env0 l)
in (match (uu____7496) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (expected_typ1, uu____7512) -> begin
(

let inferred_typ = (

let body = (match (binders) with
| [] -> begin
typ
end
| uu____7543 -> begin
(

let uu____7544 = (

let uu____7551 = (

let uu____7552 = (

let uu____7567 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____7567)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7552))
in (FStar_Syntax_Syntax.mk uu____7551))
in (uu____7544 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in ((univs2), (body)))
in (match ((Prims.op_Equality (FStar_List.length univs2) (FStar_List.length (FStar_Pervasives_Native.fst expected_typ1)))) with
| true -> begin
(

let uu____7589 = (FStar_TypeChecker_Env.inst_tscheme inferred_typ)
in (match (uu____7589) with
| (uu____7594, inferred) -> begin
(

let uu____7596 = (FStar_TypeChecker_Env.inst_tscheme expected_typ1)
in (match (uu____7596) with
| (uu____7601, expected) -> begin
(

let uu____7603 = (FStar_TypeChecker_Rel.teq_nosmt_force env0 inferred expected)
in (match (uu____7603) with
| true -> begin
()
end
| uu____7606 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end))
end))
end
| uu____7608 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end)))
end
| uu____7610 -> begin
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

let uu____7721 = (

let uu____7728 = (

let uu____7729 = (

let uu____7736 = (

let uu____7739 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7739))
in ((uu____7736), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7729))
in (FStar_Syntax_Syntax.mk uu____7728))
in (uu____7721 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7773 -> (match (uu____7773) with
| (x, imp) -> begin
(

let uu____7792 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7792), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____7796 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7796))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7811 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (

let uu____7819 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar uu____7819 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____7821 = (

let uu____7824 = (

let uu____7827 = (

let uu____7832 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7833 = (

let uu____7834 = (

let uu____7843 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7843))
in (uu____7834)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7832 uu____7833)))
in (uu____7827 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____7824))
in (FStar_Syntax_Util.refine x uu____7821)))
in (

let uu____7868 = (

let uu___1086_7869 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___1086_7869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1086_7869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7868)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7886 = (FStar_List.map (fun uu____7910 -> (match (uu____7910) with
| (x, uu____7924) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7886 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7983 -> (match (uu____7983) with
| (x, uu____7997) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let early_prims_inductive = ((

let uu____8008 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____8008)) && (FStar_List.existsb (fun s -> (Prims.op_Equality s tc.FStar_Ident.ident.FStar_Ident.idText)) early_prims_inductives))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____8020 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = (early_prims_inductive || (

let uu____8029 = (

let uu____8031 = (FStar_TypeChecker_Env.current_module env)
in uu____8031.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8029)))
in (

let quals = (

let uu____8035 = (FStar_List.filter (fun uu___4_8039 -> (match (uu___4_8039) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
true
end
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____8044 -> begin
false
end)) iquals)
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____8049 -> begin
[]
end)) uu____8035))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____8082 = (

let uu____8083 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8083))
in (FStar_Syntax_Syntax.mk_Total uu____8082))
in (

let uu____8084 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8084)))
in (

let decl = (

let uu____8088 = (FStar_Ident.range_of_lid discriminator_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____8088; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____8090 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8090) with
| true -> begin
(

let uu____8094 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____8094))
end
| uu____8097 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8102 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____8110 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8155 -> (match (uu____8155) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____8180 = (

let uu____8183 = (

let uu____8184 = (

let uu____8191 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8191), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8184))
in (pos uu____8183))
in ((uu____8180), (b)))
end
| uu____8197 -> begin
(

let uu____8199 = (

let uu____8202 = (

let uu____8203 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8203))
in (pos uu____8202))
in ((uu____8199), (b)))
end))
end))))
in (

let pat_true = (

let uu____8222 = (

let uu____8225 = (

let uu____8226 = (

let uu____8240 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8240), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8226))
in (pos uu____8225))
in ((uu____8222), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____8275 = (

let uu____8278 = (

let uu____8279 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8279))
in (pos uu____8278))
in ((uu____8275), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____8293 = (

let uu____8300 = (

let uu____8301 = (

let uu____8324 = (

let uu____8341 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____8356 = (

let uu____8373 = (FStar_Syntax_Util.branch pat_false)
in (uu____8373)::[])
in (uu____8341)::uu____8356))
in ((arg_exp), (uu____8324)))
in FStar_Syntax_Syntax.Tm_match (uu____8301))
in (FStar_Syntax_Syntax.mk uu____8300))
in (uu____8293 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____8449 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8449) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____8456 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8468 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8471 = (

let uu____8476 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____8476))
in (

let uu____8477 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in (FStar_Syntax_Util.mk_letbinding uu____8471 uvs lbtyp FStar_Parser_Const.effect_Tot_lid uu____8477 [] FStar_Range.dummyRange)))
in (

let impl = (

let uu____8483 = (

let uu____8484 = (

let uu____8491 = (

let uu____8494 = (

let uu____8495 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8495 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8494)::[])
in ((((false), ((lb)::[]))), (uu____8491)))
in FStar_Syntax_Syntax.Sig_let (uu____8484))
in {FStar_Syntax_Syntax.sigel = uu____8483; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____8509 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8509) with
| true -> begin
(

let uu____8513 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____8513))
end
| uu____8516 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8586 -> (match (uu____8586) with
| (a, uu____8595) -> begin
(

let uu____8600 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____8600) with
| (field_name, uu____8606) -> begin
(

let field_proj_tm = (

let uu____8608 = (

let uu____8609 = (FStar_Syntax_Syntax.lid_as_fv field_name (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8609))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8608 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____8635 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8677 -> (match (uu____8677) with
| (x, uu____8688) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____8694 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____8694) with
| (field_name, uu____8702) -> begin
(

let t = (

let uu____8706 = (

let uu____8707 = (

let uu____8710 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____8710))
in (FStar_Syntax_Util.arrow binders uu____8707))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8706))
in (

let only_decl = (early_prims_inductive || (

let uu____8716 = (

let uu____8718 = (FStar_TypeChecker_Env.current_module env)
in uu____8718.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8716)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____8737 = (FStar_List.filter (fun uu___5_8741 -> (match (uu___5_8741) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____8744 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____8737)
end
| uu____8746 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___6_8759 -> (match (uu___6_8759) with
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
true
end
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____8765 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____8773 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = (

let uu____8776 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____8776; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____8778 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8778) with
| true -> begin
(

let uu____8782 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____8782))
end
| uu____8785 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8790 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8836 -> (match (uu____8836) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____8862 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____8862), (b)))
end
| uu____8868 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____8878 = (

let uu____8881 = (

let uu____8882 = (

let uu____8889 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8889), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8882))
in (pos uu____8881))
in ((uu____8878), (b)))
end
| uu____8895 -> begin
(

let uu____8897 = (

let uu____8900 = (

let uu____8901 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8901))
in (pos uu____8900))
in ((uu____8897), (b)))
end)
end))
end))))
in (

let pat = (

let uu____8920 = (

let uu____8923 = (

let uu____8924 = (

let uu____8938 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8938), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8924))
in (pos uu____8923))
in (

let uu____8948 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____8920), (FStar_Pervasives_Native.None), (uu____8948))))
in (

let body = (

let uu____8964 = (

let uu____8971 = (

let uu____8972 = (

let uu____8995 = (

let uu____9012 = (FStar_Syntax_Util.branch pat)
in (uu____9012)::[])
in ((arg_exp), (uu____8995)))
in FStar_Syntax_Syntax.Tm_match (uu____8972))
in (FStar_Syntax_Syntax.mk uu____8971))
in (uu____8964 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____9077 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____9077) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____9084 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____9093 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____9096 = (

let uu____9101 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____9101))
in (

let uu____9102 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____9096; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____9102; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange}))
in (

let impl = (

let uu____9108 = (

let uu____9109 = (

let uu____9116 = (

let uu____9119 = (

let uu____9120 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____9120 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____9119)::[])
in ((((false), ((lb)::[]))), (uu____9116)))
in FStar_Syntax_Syntax.Sig_let (uu____9109))
in {FStar_Syntax_Syntax.sigel = uu____9108; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____9134 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____9134) with
| true -> begin
(

let uu____9138 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____9138))
end
| uu____9141 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____9146 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____8635 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses))))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____9192) when (

let uu____9199 = (FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid)
in (not (uu____9199))) -> begin
(

let uu____9201 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9201) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____9223 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____9223) with
| (formals, uu____9241) -> begin
(

let uu____9262 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____9297 = (

let uu____9299 = (

let uu____9300 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____9300))
in (FStar_Ident.lid_equals typ_lid uu____9299))
in (match (uu____9297) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9322, uvs', tps, typ0, uu____9326, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____9346 -> begin
(failwith "Impossible")
end)
end
| uu____9357 -> begin
FStar_Pervasives_Native.None
end))))
in (match (tps_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9395 = (FStar_Ident.lid_equals typ_lid FStar_Parser_Const.exn_lid)
in (match (uu____9395) with
| true -> begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end
| uu____9413 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____9262) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____9433 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____9433) with
| (indices, uu____9451) -> begin
(

let refine_domain = (

let uu____9474 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___7_9481 -> (match (uu___7_9481) with
| FStar_Syntax_Syntax.RecordConstructor (uu____9483) -> begin
true
end
| uu____9493 -> begin
false
end))))
in (match (uu____9474) with
| true -> begin
false
end
| uu____9498 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___8_9508 -> (match (uu___8_9508) with
| FStar_Syntax_Syntax.RecordConstructor (uu____9511, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____9523 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____9524 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____9524) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| FStar_Pervasives_Native.Some (q) -> begin
q
end)))
in (

let iquals1 = (match (((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private iquals))))) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____9534 -> begin
iquals
end)
in (

let fields = (

let uu____9537 = (FStar_Util.first_N n_typars formals)
in (match (uu____9537) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____9620 uu____9621 -> (match (((uu____9620), (uu____9621))) with
| ((x, uu____9647), (x', uu____9649)) -> begin
(

let uu____9670 = (

let uu____9677 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____9677)))
in FStar_Syntax_Syntax.NT (uu____9670))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____9682 -> begin
[]
end))




