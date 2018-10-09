
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

let uu____290 = (FStar_All.pipe_right s.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Unopteq))
in (not (uu____290)))) || (FStar_TypeChecker_Rel.teq_nosmt_force env1 t t_type))
in ((match ((not (valid_type))) with
| true -> begin
(

let uu____294 = (

let uu____299 = (

let uu____300 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____301 = (FStar_Ident.string_of_lid tc)
in (FStar_Util.format2 "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier" uu____300 uu____301)))
in ((FStar_Errors.Error_InductiveAnnotNotAType), (uu____299)))
in (FStar_Errors.raise_error uu____294 s.FStar_Syntax_Syntax.sigrng))
end
| uu____302 -> begin
()
end);
(

let usubst1 = (FStar_Syntax_Subst.univ_var_closing uvs1)
in (

let guard1 = (FStar_TypeChecker_Util.close_guard_implicits env1 tps3 guard)
in (

let t_tc = (

let uu____310 = (

let uu____319 = (FStar_All.pipe_right tps3 (FStar_Syntax_Subst.subst_binders usubst1))
in (

let uu____336 = (

let uu____345 = (

let uu____358 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps3) usubst1)
in (FStar_Syntax_Subst.subst_binders uu____358))
in (FStar_All.pipe_right indices uu____345))
in (FStar_List.append uu____319 uu____336)))
in (

let uu____381 = (

let uu____384 = (

let uu____385 = (

let uu____390 = (FStar_Syntax_Subst.shift_subst ((FStar_List.length tps3) + (FStar_List.length indices)) usubst1)
in (FStar_Syntax_Subst.subst uu____390))
in (FStar_All.pipe_right t uu____385))
in (FStar_Syntax_Syntax.mk_Total uu____384))
in (FStar_Syntax_Util.arrow uu____310 uu____381)))
in (

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let k4 = (FStar_Syntax_Subst.close tps4 k3)
in (

let uu____407 = (

let uu____412 = (FStar_Syntax_Subst.subst_binders usubst1 tps4)
in (

let uu____413 = (

let uu____414 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps4) usubst1)
in (FStar_Syntax_Subst.subst uu____414 k4))
in ((uu____412), (uu____413))))
in (match (uu____407) with
| (tps5, k5) -> begin
(

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____434 = (FStar_TypeChecker_Env.push_let_binding env0 (FStar_Util.Inr (fv_tc)) ((uvs1), (t_tc)))
in ((uu____434), ((

let uu___365_440 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps5), (k5), (mutuals), (data))); FStar_Syntax_Syntax.sigrng = uu___365_440.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___365_440.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___365_440.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___365_440.FStar_Syntax_Syntax.sigattrs})), (u), (guard1))))
end)))))));
))
end)))
end))
end))
end))
end))
end)))
end
| uu____445 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, _mutual_tcs) -> begin
(

let uu____505 = (FStar_Syntax_Subst.univ_var_opening _uvs)
in (match (uu____505) with
| (usubst, _uvs1) -> begin
(

let uu____528 = (

let uu____533 = (FStar_TypeChecker_Env.push_univ_vars env _uvs1)
in (

let uu____534 = (FStar_Syntax_Subst.subst usubst t)
in ((uu____533), (uu____534))))
in (match (uu____528) with
| (env1, t1) -> begin
(

let uu____541 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____580 -> (match (uu____580) with
| (se1, u_tc) -> begin
(

let uu____595 = (

let uu____596 = (

let uu____597 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____597))
in (FStar_Ident.lid_equals tc_lid uu____596))
in (match (uu____595) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____616, uu____617, tps, uu____619, uu____620, uu____621) -> begin
(

let tps1 = (

let uu____631 = (FStar_All.pipe_right tps (FStar_Syntax_Subst.subst_binders usubst))
in (FStar_All.pipe_right uu____631 (FStar_List.map (fun uu____671 -> (match (uu____671) with
| (x, uu____685) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____693 = (

let uu____700 = (FStar_TypeChecker_Env.push_binders env1 tps2)
in ((uu____700), (tps2), (u_tc)))
in FStar_Pervasives_Native.Some (uu____693))))
end
| uu____707 -> begin
(failwith "Impossible")
end)
end
| uu____716 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (tps_u_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____748 = (FStar_Ident.lid_equals tc_lid FStar_Parser_Const.exn_lid)
in (match (uu____748) with
| true -> begin
((env1), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____761 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____541) with
| (env2, tps, u_tc) -> begin
(

let uu____775 = (

let t2 = (FStar_TypeChecker_Normalize.normalize (FStar_List.append FStar_TypeChecker_Normalize.whnf_steps ((FStar_TypeChecker_Env.AllowUnboundUniverses)::[])) env2 t1)
in (

let uu____791 = (

let uu____792 = (FStar_Syntax_Subst.compress t2)
in uu____792.FStar_Syntax_Syntax.n)
in (match (uu____791) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____831 = (FStar_Util.first_N ntps bs)
in (match (uu____831) with
| (uu____872, bs') -> begin
(

let t3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____943 -> (match (uu____943) with
| (x, uu____951) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____956 = (FStar_Syntax_Subst.subst subst1 t3)
in (FStar_Syntax_Util.arrow_formals uu____956))))
end))
end
| uu____957 -> begin
(([]), (t2))
end)))
in (match (uu____775) with
| (arguments, result) -> begin
((

let uu____1001 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____1001) with
| true -> begin
(

let uu____1002 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____1003 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____1004 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____1002 uu____1003 uu____1004))))
end
| uu____1005 -> begin
()
end));
(

let uu____1006 = (FStar_TypeChecker_TcTerm.tc_tparams env2 arguments)
in (match (uu____1006) with
| (arguments1, env', us) -> begin
(

let uu____1020 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____1020) with
| (result1, res_lcomp) -> begin
(

let uu____1031 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____1031) with
| (head1, args) -> begin
(

let p_args = (

let uu____1089 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_Pervasives_Native.fst uu____1089))
in ((FStar_List.iter2 (fun uu____1171 uu____1172 -> (match (((uu____1171), (uu____1172))) with
| ((bv, uu____1202), (t2, uu____1204)) -> begin
(

let uu____1231 = (

let uu____1232 = (FStar_Syntax_Subst.compress t2)
in uu____1232.FStar_Syntax_Syntax.n)
in (match (uu____1231) with
| FStar_Syntax_Syntax.Tm_name (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
()
end
| uu____1236 -> begin
(

let uu____1237 = (

let uu____1242 = (

let uu____1243 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____1244 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "This parameter is not constant: expected %s, got %s" uu____1243 uu____1244)))
in ((FStar_Errors.Error_BadInductiveParam), (uu____1242)))
in (FStar_Errors.raise_error uu____1237 t2.FStar_Syntax_Syntax.pos))
end))
end)) tps p_args);
(

let ty = (

let uu____1246 = (unfold_whnf env2 res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_right uu____1246 FStar_Syntax_Util.unrefine))
in ((

let uu____1248 = (

let uu____1249 = (FStar_Syntax_Subst.compress ty)
in uu____1249.FStar_Syntax_Syntax.n)
in (match (uu____1248) with
| FStar_Syntax_Syntax.Tm_type (uu____1252) -> begin
()
end
| uu____1253 -> begin
(

let uu____1254 = (

let uu____1259 = (

let uu____1260 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____1261 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____1260 uu____1261)))
in ((FStar_Errors.Fatal_WrongResultTypeAfterConstrutor), (uu____1259)))
in (FStar_Errors.raise_error uu____1254 se.FStar_Syntax_Syntax.sigrng))
end));
(

let g_uvs = (

let uu____1263 = (

let uu____1264 = (FStar_Syntax_Subst.compress head1)
in uu____1264.FStar_Syntax_Syntax.n)
in (match (uu____1263) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1268; FStar_Syntax_Syntax.vars = uu____1269}, tuvs) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
(match ((Prims.op_Equality (FStar_List.length _uvs1) (FStar_List.length tuvs))) with
| true -> begin
(FStar_List.fold_left2 (fun g u1 u2 -> (

let uu____1282 = (

let uu____1283 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____1284 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u2))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_TypeChecker_Rel.teq env' uu____1283 uu____1284)))
in (FStar_TypeChecker_Env.conj_guard g uu____1282))) FStar_TypeChecker_Env.trivial_guard tuvs _uvs1)
end
| uu____1285 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedConstructorType), ("Length of annotated universes does not match inferred universes")) se.FStar_Syntax_Syntax.sigrng)
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
FStar_TypeChecker_Env.trivial_guard
end
| uu____1287 -> begin
(

let uu____1288 = (

let uu____1293 = (

let uu____1294 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____1295 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____1294 uu____1295)))
in ((FStar_Errors.Fatal_UnexpectedConstructorType), (uu____1293)))
in (FStar_Errors.raise_error uu____1288 se.FStar_Syntax_Syntax.sigrng))
end))
in (

let g = (FStar_List.fold_left2 (fun g uu____1310 u_x -> (match (uu____1310) with
| (x, uu____1319) -> begin
(

let uu____1324 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Env.conj_guard g uu____1324))
end)) g_uvs arguments1 us)
in (

let t2 = (

let uu____1328 = (

let uu____1337 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____1377 -> (match (uu____1377) with
| (x, uu____1391) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____1337 arguments1))
in (

let uu____1404 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____1328 uu____1404)))
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars _uvs1 t2)
in (((

let uu___366_1409 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), (_uvs1), (t3), (tc_lid), (ntps), ([]))); FStar_Syntax_Syntax.sigrng = uu___366_1409.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___366_1409.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___366_1409.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___366_1409.FStar_Syntax_Syntax.sigattrs})), (g))))));
));
))
end))
end))
end));
)
end))
end))
end))
end))
end
| uu____1412 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map FStar_Pervasives_Native.snd tcs)
in (

let g1 = (

let uu___367_1477 = g
in {FStar_TypeChecker_Env.guard_f = uu___367_1477.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___367_1477.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((FStar_Pervasives_Native.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___367_1477.FStar_TypeChecker_Env.implicits})
in ((

let uu____1487 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1487) with
| true -> begin
(

let uu____1488 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____1488))
end
| uu____1489 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____1528 -> (match (uu____1528) with
| (se, uu____1534) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____1535, uu____1536, tps, k, uu____1539, uu____1540) -> begin
(

let uu____1549 = (

let uu____1550 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____1550))
in (FStar_Syntax_Syntax.null_binder uu____1549))
end
| uu____1555 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1583, uu____1584, t, uu____1586, uu____1587, uu____1588) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____1593 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____1597 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____1597))
in ((

let uu____1607 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1607) with
| true -> begin
(

let uu____1608 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____1608))
end
| uu____1609 -> begin
()
end));
(

let uu____1610 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____1610) with
| (uvs, t1) -> begin
((

let uu____1630 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____1630) with
| true -> begin
(

let uu____1631 = (

let uu____1632 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____1632 (FStar_String.concat ", ")))
in (

let uu____1643 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____1631 uu____1643)))
end
| uu____1644 -> begin
()
end));
(

let uu____1645 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____1645) with
| (uvs1, t2) -> begin
(

let uu____1660 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____1660) with
| (args, uu____1684) -> begin
(

let uu____1705 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____1705) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____1810 uu____1811 -> (match (((uu____1810), (uu____1811))) with
| ((x, uu____1833), (se, uu____1835)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____1851, tps, uu____1853, mutuals, datas1) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____1865 = (

let uu____1870 = (

let uu____1871 = (FStar_Syntax_Subst.compress ty)
in uu____1871.FStar_Syntax_Syntax.n)
in (match (uu____1870) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____1900 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____1900) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1978 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos)
end)
in ((tps1), (t3)))
end))
end
| uu____1997 -> begin
(([]), (ty))
end))
in (match (uu____1865) with
| (tps1, t3) -> begin
(

let uu___368_2006 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1))); FStar_Syntax_Syntax.sigrng = uu___368_2006.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___368_2006.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___368_2006.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___368_2006.FStar_Syntax_Syntax.sigattrs})
end)))
end
| uu____2011 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____2017 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_1 -> FStar_Syntax_Syntax.U_name (_0_1))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___356_2039 -> (match (uu___356_2039) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2045, uu____2046, uu____2047, uu____2048, uu____2049); FStar_Syntax_Syntax.sigrng = uu____2050; FStar_Syntax_Syntax.sigquals = uu____2051; FStar_Syntax_Syntax.sigmeta = uu____2052; FStar_Syntax_Syntax.sigattrs = uu____2053} -> begin
((tc), (uvs_universes))
end
| uu____2066 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____2089 d -> (match (uu____2089) with
| (t3, uu____2098) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____2104, uu____2105, tc, ntps, mutuals) -> begin
(

let ty = (

let uu____2114 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2114 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___369_2115 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___369_2115.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___369_2115.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___369_2115.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___369_2115.FStar_Syntax_Syntax.sigattrs}))
end
| uu____2118 -> begin
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

let uu____2133 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____2133) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____2134 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____2145 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____2145)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____2161 = (

let uu____2162 = (FStar_Syntax_Subst.compress t)
in uu____2162.FStar_Syntax_Syntax.n)
in (match (uu____2161) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____2181 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____2186 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____2239 = (FStar_ST.op_Bang unfolded)
in (FStar_List.existsML (fun uu____2308 -> (match (uu____2308) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____2351 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (FStar_Pervasives_Native.fst uu____2351))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt_force env (FStar_Pervasives_Native.fst a) (FStar_Pervasives_Native.fst a')))) true args l)))
end)) uu____2239)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____2595 = (

let uu____2596 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____2596))
in (debug_log env uu____2595));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____2599 = (

let uu____2600 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____2600))
in (debug_log env uu____2599));
((

let uu____2603 = (ty_occurs_in ty_lid btype1)
in (not (uu____2603))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____2614 = (

let uu____2615 = (FStar_Syntax_Subst.compress btype1)
in uu____2615.FStar_Syntax_Syntax.n)
in (match (uu____2614) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____2644 = (try_get_fv t)
in (match (uu____2644) with
| (fv, us) -> begin
(

let uu____2651 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)
in (match (uu____2651) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____2663 -> (match (uu____2663) with
| (t1, uu____2671) -> begin
(

let uu____2676 = (ty_occurs_in ty_lid t1)
in (not (uu____2676)))
end)) args);
)
end
| uu____2677 -> begin
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

let uu____2726 = (FStar_TypeChecker_Env.unfold_effect_abbrev env c)
in (FStar_All.pipe_right uu____2726 FStar_Syntax_Syntax.mk_Comp))
in ((FStar_Syntax_Util.is_pure_or_ghost_comp c1) || (

let uu____2730 = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c1))
in (FStar_All.pipe_right uu____2730 (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.TotalEffect)))))))
in (match ((not (check_comp1))) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____2738 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____2750 -> (match (uu____2750) with
| (b, uu____2758) -> begin
(

let uu____2763 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____2763)))
end)) sbs) && (

let uu____2768 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____2768) with
| (uu____2773, return_type) -> begin
(

let uu____2775 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____2775))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2796) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____2798) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2801) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____2828) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____2854, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____2912 -> (match (uu____2912) with
| (p, uu____2924, t) -> begin
(

let bs = (

let uu____2943 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____2943))
in (

let uu____2952 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2952) with
| (bs1, t1) -> begin
(

let uu____2959 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____2959))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____2981, uu____2982) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____3044 -> begin
((

let uu____3046 = (

let uu____3047 = (

let uu____3048 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____3049 = (

let uu____3050 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____3050))
in (Prims.strcat uu____3048 uu____3049)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____3047))
in (debug_log env uu____3046));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____3068 = (

let uu____3069 = (

let uu____3070 = (

let uu____3071 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____3071))
in (Prims.strcat ilid.FStar_Ident.str uu____3070))
in (Prims.strcat "Checking nested positivity in the inductive " uu____3069))
in (debug_log env uu____3068));
(

let uu____3072 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____3072) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
(

let uu____3085 = (

let uu____3086 = (FStar_Syntax_Syntax.lid_as_fv ilid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Env.fv_has_attr env uu____3086 FStar_Parser_Const.assume_strictly_positive_attr_lid))
in (match (uu____3085) with
| true -> begin
((

let uu____3088 = (

let uu____3089 = (FStar_Ident.string_of_lid ilid)
in (FStar_Util.format1 "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true" uu____3089))
in (debug_log env uu____3088));
true;
)
end
| uu____3090 -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end))
end
| uu____3092 -> begin
(

let uu____3093 = (already_unfolded ilid args unfolded env)
in (match (uu____3093) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____3115 -> begin
(

let num_ibs = (

let uu____3117 = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in (FStar_Option.get uu____3117))
in ((

let uu____3121 = (

let uu____3122 = (

let uu____3123 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____3123 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____3122))
in (debug_log env uu____3121));
(

let uu____3125 = (

let uu____3126 = (FStar_ST.op_Bang unfolded)
in (

let uu____3172 = (

let uu____3179 = (

let uu____3184 = (

let uu____3185 = (FStar_List.splitAt num_ibs args)
in (FStar_Pervasives_Native.fst uu____3185))
in ((ilid), (uu____3184)))
in (uu____3179)::[])
in (FStar_List.append uu____3126 uu____3172)))
in (FStar_ST.op_Colon_Equals unfolded uu____3125));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____3330 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3330) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3352 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____3355 = (

let uu____3356 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____3356))
in (debug_log env uu____3355));
(

let uu____3357 = (

let uu____3358 = (FStar_Syntax_Subst.compress dt1)
in uu____3358.FStar_Syntax_Syntax.n)
in (match (uu____3357) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____3384 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____3384) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____3447 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____3447 dbs1))
in (

let c1 = (

let uu____3451 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____3451 c))
in (

let uu____3454 = (FStar_List.splitAt num_ibs args)
in (match (uu____3454) with
| (args1, uu____3488) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst ib)), ((FStar_Pervasives_Native.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____3580 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____3580 c1))
in ((

let uu____3590 = (

let uu____3591 = (

let uu____3592 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____3593 = (

let uu____3594 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____3594))
in (Prims.strcat uu____3592 uu____3593)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____3591))
in (debug_log env uu____3590));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____3625 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____3627 = (

let uu____3628 = (FStar_Syntax_Subst.compress dt1)
in uu____3628.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____3627 ilid num_ibs unfolded env));
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

let uu____3694 = (try_get_fv t1)
in (match (uu____3694) with
| (fv, uu____3700) -> begin
(

let uu____3701 = (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)
in (match (uu____3701) with
| true -> begin
true
end
| uu____3702 -> begin
(failwith "Impossible, expected the type to be ilid")
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____3726 = (

let uu____3727 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____3727))
in (debug_log env uu____3726));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____3729 = (FStar_List.fold_left (fun uu____3748 b -> (match (uu____3748) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____3770 -> begin
(

let uu____3771 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____3794 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____3771), (uu____3794))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____3729) with
| (b, uu____3808) -> begin
b
end)));
)
end
| uu____3809 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____3860 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3860) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____3882 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____3884 = (

let uu____3885 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____3885))
in (debug_log env uu____3884));
(

let uu____3886 = (

let uu____3887 = (FStar_Syntax_Subst.compress dt)
in uu____3887.FStar_Syntax_Syntax.n)
in (match (uu____3886) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3890) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3893) -> begin
(

let dbs1 = (

let uu____3923 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (FStar_Pervasives_Native.snd uu____3923))
in (

let dbs2 = (

let uu____3973 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____3973 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____3978 = (

let uu____3979 = (

let uu____3980 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____3980 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____3979))
in (debug_log env uu____3978));
(

let uu____3987 = (FStar_List.fold_left (fun uu____4006 b -> (match (uu____4006) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____4028 -> begin
(

let uu____4029 = (ty_strictly_positive_in_type ty_lid (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____4052 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____4029), (uu____4052))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____3987) with
| (b, uu____4066) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____4067, uu____4068) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, univs1) -> begin
((debug_log env "Data constructor type is a Tm_uinst, so recursing in the base type");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____4121 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____4139 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____4155, uu____4156, uu____4157) -> begin
((lid), (us), (bs))
end
| uu____4166 -> begin
(failwith "Impossible!")
end)
in (match (uu____4139) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____4176 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____4176) with
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

let uu____4199 = (

let uu____4202 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (FStar_Pervasives_Native.snd uu____4202))
in (FStar_List.for_all (fun d -> (

let uu____4214 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____4214 unfolded_inductives env2))) uu____4199))))))
end))
end))))


let check_exn_positivity : FStar_Ident.lid  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun data_ctor_lid env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (ty_positive_in_datacon FStar_Parser_Const.exn_lid data_ctor_lid [] [] unfolded_inductives env)))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4289, uu____4290, t, uu____4292, uu____4293, uu____4294) -> begin
t
end
| uu____4299 -> begin
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

let uu____4319 = (

let uu____4320 = (FStar_String.substring str (len - haseq_suffix_len) haseq_suffix_len)
in (FStar_String.compare uu____4320 haseq_suffix))
in (Prims.op_Equality uu____4319 (Prims.parse_int "0"))))))))


let get_haseq_axiom_lid : FStar_Ident.lid  ->  FStar_Ident.lid = (fun lid -> (

let uu____4340 = (

let uu____4343 = (

let uu____4346 = (FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText haseq_suffix))
in (uu____4346)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____4343))
in (FStar_Ident.lid_of_ids uu____4340)))


let get_optimized_haseq_axiom : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_names  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun en ty usubst us -> (

let uu____4391 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4405, bs, t, uu____4408, uu____4409) -> begin
((lid), (bs), (t))
end
| uu____4418 -> begin
(failwith "Impossible!")
end)
in (match (uu____4391) with
| (lid, bs, t) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____4440 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____4440 t))
in (

let uu____4449 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____4449) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____4467 = (

let uu____4468 = (FStar_Syntax_Subst.compress t2)
in uu____4468.FStar_Syntax_Syntax.n)
in (match (uu____4467) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4472) -> begin
ibs
end
| uu____4493 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____4502 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____4503 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4502 uu____4503)))
in (

let ind1 = (

let uu____4509 = (

let uu____4514 = (FStar_List.map (fun uu____4531 -> (match (uu____4531) with
| (bv, aq) -> begin
(

let uu____4550 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4550), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4514))
in (uu____4509 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____4558 = (

let uu____4563 = (FStar_List.map (fun uu____4580 -> (match (uu____4580) with
| (bv, aq) -> begin
(

let uu____4599 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4599), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4563))
in (uu____4558 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____4607 = (

let uu____4612 = (

let uu____4613 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____4613)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4612))
in (uu____4607 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____4664 = (

let uu____4665 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____4665))
in (FStar_TypeChecker_Rel.subtype_nosmt_force en (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort uu____4664))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____4678 = (

let uu____4681 = (

let uu____4686 = (

let uu____4687 = (

let uu____4696 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b))
in (FStar_Syntax_Syntax.as_arg uu____4696))
in (uu____4687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4686))
in (uu____4681 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____4678))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___370_4721 = fml
in (

let uu____4722 = (

let uu____4723 = (

let uu____4730 = (

let uu____4731 = (

let uu____4744 = (

let uu____4755 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____4755)::[])
in (uu____4744)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____4731))
in ((fml), (uu____4730)))
in FStar_Syntax_Syntax.Tm_meta (uu____4723))
in {FStar_Syntax_Syntax.n = uu____4722; FStar_Syntax_Syntax.pos = uu___370_4721.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___370_4721.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____4810 = (

let uu____4815 = (

let uu____4816 = (

let uu____4825 = (

let uu____4826 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4826 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4825))
in (uu____4816)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4815))
in (uu____4810 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____4883 = (

let uu____4888 = (

let uu____4889 = (

let uu____4898 = (

let uu____4899 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____4899 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____4898))
in (uu____4889)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4888))
in (uu____4883 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
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

let uu____4975 = (

let uu____4976 = (FStar_Syntax_Subst.compress dt1)
in uu____4976.FStar_Syntax_Syntax.n)
in (match (uu____4975) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4980) -> begin
(

let dbs1 = (

let uu____5010 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____5010))
in (

let dbs2 = (

let uu____5060 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5060 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____5075 = (

let uu____5080 = (

let uu____5081 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____5081)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5080))
in (uu____5075 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sort_range = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____5114 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____5114 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____5122 = (

let uu____5127 = (

let uu____5128 = (

let uu____5137 = (

let uu____5138 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____5138 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____5137))
in (uu____5128)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5127))
in (uu____5122 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____5187 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty : FStar_Syntax_Syntax.sigelts  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.sigelt  ->  ((FStar_Ident.lident * FStar_Syntax_Syntax.term) Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun all_datas_in_the_bundle usubst us acc ty -> (

let lid = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5277, uu____5278, uu____5279, uu____5280, uu____5281) -> begin
lid
end
| uu____5290 -> begin
(failwith "Impossible!")
end)
in (

let uu____5291 = acc
in (match (uu____5291) with
| (uu____5328, en, uu____5330, uu____5331) -> begin
(

let uu____5352 = (get_optimized_haseq_axiom en ty usubst us)
in (match (uu____5352) with
| (axiom_lid, fml, bs, ibs, haseq_bs) -> begin
(

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____5389 = acc
in (match (uu____5389) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5463, uu____5464, uu____5465, t_lid, uu____5467, uu____5468) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____5473 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____5486 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc1 uu____5486))) FStar_Syntax_Util.t_true t_datas)
in (

let uu____5489 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____5492 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env2), (uu____5489), (uu____5492))))))))
end)))
end))
end))))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let uu____5549 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5559, us, uu____5561, t, uu____5563, uu____5564) -> begin
((us), (t))
end
| uu____5573 -> begin
(failwith "Impossible!")
end))
in (match (uu____5549) with
| (us, t) -> begin
(

let uu____5582 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5582) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____5607 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____5607) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (

let uu____5685 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____5685) with
| (uu____5700, t1) -> begin
(

let uu____5722 = (FStar_Syntax_Util.is_eqtype_no_unrefine t1)
in (match (uu____5722) with
| true -> begin
cond
end
| uu____5723 -> begin
(FStar_Syntax_Util.mk_imp guard cond)
end))
end))
in (

let uu____5724 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____5724) with
| (phi1, uu____5732) -> begin
((

let uu____5734 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____5734) with
| true -> begin
(

let uu____5735 = (FStar_TypeChecker_Env.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____5735))
end
| uu____5736 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____5752 -> (match (uu____5752) with
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

let uu____5820 = (

let uu____5821 = (FStar_Syntax_Subst.compress t)
in uu____5821.FStar_Syntax_Syntax.n)
in (match (uu____5820) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____5828) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____5865 = (is_mutual t')
in (match (uu____5865) with
| true -> begin
true
end
| uu____5866 -> begin
(

let uu____5867 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (exists_mutual uu____5867))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____5887) -> begin
(is_mutual t')
end
| uu____5892 -> begin
false
end)))
and exists_mutual = (fun uu___357_5893 -> (match (uu___357_5893) with
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

let uu____5912 = (

let uu____5913 = (FStar_Syntax_Subst.compress dt1)
in uu____5913.FStar_Syntax_Syntax.n)
in (match (uu____5912) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5919) -> begin
(

let dbs1 = (

let uu____5949 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (FStar_Pervasives_Native.snd uu____5949))
in (

let dbs2 = (

let uu____5999 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5999 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____6019 = (

let uu____6024 = (

let uu____6025 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (uu____6025)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____6024))
in (uu____6019 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____6057 = (is_mutual sort)
in (match (uu____6057) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____6060 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____6069 = (

let uu____6074 = (

let uu____6075 = (

let uu____6084 = (

let uu____6085 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____6085 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____6084))
in (uu____6075)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____6074))
in (uu____6069 FStar_Pervasives_Native.None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____6134 -> begin
acc
end))))))


let unoptimized_haseq_ty : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____6183 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6205, bs, t, uu____6208, d_lids) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____6220 -> begin
(failwith "Impossible!")
end)
in (match (uu____6183) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____6243 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____6243 t))
in (

let uu____6252 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____6252) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____6262 = (

let uu____6263 = (FStar_Syntax_Subst.compress t2)
in uu____6263.FStar_Syntax_Syntax.n)
in (match (uu____6262) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____6267) -> begin
ibs
end
| uu____6288 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____6297 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____6298 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6297 uu____6298)))
in (

let ind1 = (

let uu____6304 = (

let uu____6309 = (FStar_List.map (fun uu____6326 -> (match (uu____6326) with
| (bv, aq) -> begin
(

let uu____6345 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____6345), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____6309))
in (uu____6304 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____6353 = (

let uu____6358 = (FStar_List.map (fun uu____6375 -> (match (uu____6375) with
| (bv, aq) -> begin
(

let uu____6394 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____6394), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6358))
in (uu____6353 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____6402 = (

let uu____6407 = (

let uu____6408 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____6408)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____6407))
in (uu____6402 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____6446, uu____6447, uu____6448, t_lid, uu____6450, uu____6451) -> begin
(Prims.op_Equality t_lid lid)
end
| uu____6456 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___371_6466 = fml
in (

let uu____6467 = (

let uu____6468 = (

let uu____6475 = (

let uu____6476 = (

let uu____6489 = (

let uu____6500 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____6500)::[])
in (uu____6489)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____6476))
in ((fml), (uu____6475)))
in FStar_Syntax_Syntax.Tm_meta (uu____6468))
in {FStar_Syntax_Syntax.n = uu____6467; FStar_Syntax_Syntax.pos = uu___371_6466.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___371_6466.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____6555 = (

let uu____6560 = (

let uu____6561 = (

let uu____6570 = (

let uu____6571 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____6571 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____6570))
in (uu____6561)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____6560))
in (uu____6555 FStar_Pervasives_Native.None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____6628 = (

let uu____6633 = (

let uu____6634 = (

let uu____6643 = (

let uu____6644 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((FStar_Pervasives_Native.fst b)), (FStar_Pervasives_Native.None)))::[]) uu____6644 FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.as_arg uu____6643))
in (uu____6634)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____6633))
in (uu____6628 FStar_Pervasives_Native.None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6737, uu____6738, uu____6739, uu____6740, uu____6741) -> begin
lid
end
| uu____6750 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____6751 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____6763, uu____6764, uu____6765, uu____6766) -> begin
((lid), (us))
end
| uu____6775 -> begin
(failwith "Impossible!")
end))
in (match (uu____6751) with
| (lid, us) -> begin
(

let uu____6784 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____6784) with
| (usubst, us1) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us1) FStar_Syntax_Util.t_true tcs)
in (

let se = (

let uu____6811 = (

let uu____6812 = (

let uu____6819 = (get_haseq_axiom_lid lid)
in ((uu____6819), (us1), (fml)))
in FStar_Syntax_Syntax.Sig_assume (uu____6812))
in {FStar_Syntax_Syntax.sigel = uu____6811; FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (se)::[]))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____6872 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___358_6897 -> (match (uu___358_6897) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____6898); FStar_Syntax_Syntax.sigrng = uu____6899; FStar_Syntax_Syntax.sigquals = uu____6900; FStar_Syntax_Syntax.sigmeta = uu____6901; FStar_Syntax_Syntax.sigattrs = uu____6902} -> begin
true
end
| uu____6923 -> begin
false
end))))
in (match (uu____6872) with
| (tys, datas) -> begin
((

let uu____6945 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___359_6954 -> (match (uu___359_6954) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____6955); FStar_Syntax_Syntax.sigrng = uu____6956; FStar_Syntax_Syntax.sigquals = uu____6957; FStar_Syntax_Syntax.sigmeta = uu____6958; FStar_Syntax_Syntax.sigattrs = uu____6959} -> begin
false
end
| uu____6978 -> begin
true
end))))
in (match (uu____6945) with
| true -> begin
(

let uu____6979 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType), ("Mutually defined type contains a non-inductive element")) uu____6979))
end
| uu____6980 -> begin
()
end));
(

let univs1 = (match ((Prims.op_Equality (FStar_List.length tys) (Prims.parse_int "0"))) with
| true -> begin
[]
end
| uu____6986 -> begin
(

let uu____6987 = (

let uu____6988 = (FStar_List.hd tys)
in uu____6988.FStar_Syntax_Syntax.sigel)
in (match (uu____6987) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6991, uvs, uu____6993, uu____6994, uu____6995, uu____6996) -> begin
uvs
end
| uu____7005 -> begin
(failwith "Impossible, can\'t happen!")
end))
end)
in (

let env0 = env
in (

let uu____7009 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
((env), (tys), (datas))
end
| uu____7034 -> begin
(

let uu____7035 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____7035) with
| (subst1, univs2) -> begin
(

let tys1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____7073, bs, t, l1, l2) -> begin
(

let uu____7086 = (

let uu____7103 = (FStar_Syntax_Subst.subst_binders subst1 bs)
in (

let uu____7104 = (

let uu____7105 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) subst1)
in (FStar_Syntax_Subst.subst uu____7105 t))
in ((lid), (univs2), (uu____7103), (uu____7104), (l1), (l2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____7086))
end
| uu____7118 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___372_7119 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___372_7119.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___372_7119.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___372_7119.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___372_7119.FStar_Syntax_Syntax.sigattrs}))) tys)
in (

let datas1 = (FStar_List.map (fun se -> (

let sigel = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____7129, t, lid_t, x, l) -> begin
(

let uu____7138 = (

let uu____7153 = (FStar_Syntax_Subst.subst subst1 t)
in ((lid), (univs2), (uu____7153), (lid_t), (x), (l)))
in FStar_Syntax_Syntax.Sig_datacon (uu____7138))
end
| uu____7156 -> begin
(failwith "Impossible, can\'t happen")
end)
in (

let uu___373_7157 = se
in {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = uu___373_7157.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___373_7157.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___373_7157.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___373_7157.FStar_Syntax_Syntax.sigattrs}))) datas)
in (

let uu____7158 = (FStar_TypeChecker_Env.push_univ_vars env univs2)
in ((uu____7158), (tys1), (datas1)))))
end))
end)
in (match (uu____7009) with
| (env1, tys1, datas1) -> begin
(

let uu____7184 = (FStar_List.fold_right (fun tc uu____7223 -> (match (uu____7223) with
| (env2, all_tcs, g) -> begin
(

let uu____7263 = (tc_tycon env2 tc)
in (match (uu____7263) with
| (env3, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____7290 = (FStar_TypeChecker_Env.debug env3 FStar_Options.Low)
in (match (uu____7290) with
| true -> begin
(

let uu____7291 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____7291))
end
| uu____7292 -> begin
()
end));
(

let uu____7293 = (

let uu____7294 = (FStar_TypeChecker_Env.conj_guard guard g')
in (FStar_TypeChecker_Env.conj_guard g uu____7294))
in ((env3), ((((tc1), (tc_u)))::all_tcs), (uu____7293)));
))
end))
end)) tys1 ((env1), ([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____7184) with
| (env2, tcs, g) -> begin
(

let uu____7340 = (FStar_List.fold_right (fun se uu____7362 -> (match (uu____7362) with
| (datas2, g1) -> begin
(

let uu____7381 = (

let uu____7386 = (tc_data env2 tcs)
in (uu____7386 se))
in (match (uu____7381) with
| (data, g') -> begin
(

let uu____7403 = (FStar_TypeChecker_Env.conj_guard g1 g')
in (((data)::datas2), (uu____7403)))
end))
end)) datas1 (([]), (g)))
in (match (uu____7340) with
| (datas2, g1) -> begin
(

let uu____7424 = (match ((Prims.op_Equality (FStar_List.length univs1) (Prims.parse_int "0"))) with
| true -> begin
(generalize_and_inst_within env1 g1 tcs datas2)
end
| uu____7441 -> begin
(

let uu____7442 = (FStar_List.map FStar_Pervasives_Native.fst tcs)
in ((uu____7442), (datas2)))
end)
in (match (uu____7424) with
| (tcs1, datas3) -> begin
(

let sig_bndle = (

let uu____7474 = (FStar_TypeChecker_Env.get_range env0)
in (

let uu____7475 = (FStar_List.collect (fun s -> s.FStar_Syntax_Syntax.sigattrs) ses)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas3)), (lids))); FStar_Syntax_Syntax.sigrng = uu____7474; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = uu____7475}))
in ((FStar_All.pipe_right tcs1 (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs2, binders, typ, uu____7501, uu____7502) -> begin
(

let fail1 = (fun expected inferred -> (

let uu____7522 = (

let uu____7527 = (

let uu____7528 = (FStar_Syntax_Print.tscheme_to_string expected)
in (

let uu____7529 = (FStar_Syntax_Print.tscheme_to_string inferred)
in (FStar_Util.format2 "Expected an inductive with type %s; got %s" uu____7528 uu____7529)))
in ((FStar_Errors.Fatal_UnexpectedInductivetype), (uu____7527)))
in (FStar_Errors.raise_error uu____7522 se.FStar_Syntax_Syntax.sigrng)))
in (

let uu____7530 = (FStar_TypeChecker_Env.try_lookup_val_decl env0 l)
in (match (uu____7530) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (expected_typ1, uu____7546) -> begin
(

let inferred_typ = (

let body = (match (binders) with
| [] -> begin
typ
end
| uu____7577 -> begin
(

let uu____7578 = (

let uu____7585 = (

let uu____7586 = (

let uu____7601 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____7601)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7586))
in (FStar_Syntax_Syntax.mk uu____7585))
in (uu____7578 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in ((univs2), (body)))
in (match ((Prims.op_Equality (FStar_List.length univs2) (FStar_List.length (FStar_Pervasives_Native.fst expected_typ1)))) with
| true -> begin
(

let uu____7625 = (FStar_TypeChecker_Env.inst_tscheme inferred_typ)
in (match (uu____7625) with
| (uu____7630, inferred) -> begin
(

let uu____7632 = (FStar_TypeChecker_Env.inst_tscheme expected_typ1)
in (match (uu____7632) with
| (uu____7637, expected) -> begin
(

let uu____7639 = (FStar_TypeChecker_Rel.teq_nosmt_force env0 inferred expected)
in (match (uu____7639) with
| true -> begin
()
end
| uu____7640 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end))
end))
end
| uu____7641 -> begin
(fail1 expected_typ1 inferred_typ)
end))
end)))
end
| uu____7642 -> begin
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

let uu____7734 = (

let uu____7741 = (

let uu____7742 = (

let uu____7749 = (

let uu____7752 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____7752))
in ((uu____7749), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7742))
in (FStar_Syntax_Syntax.mk uu____7741))
in (uu____7734 FStar_Pervasives_Native.None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7789 -> (match (uu____7789) with
| (x, imp) -> begin
(

let uu____7808 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7808), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args FStar_Pervasives_Native.None p)))
in (

let unrefined_arg_binder = (

let uu____7812 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder uu____7812))
in (

let arg_binder = (match ((not (refine_domain))) with
| true -> begin
unrefined_arg_binder
end
| uu____7826 -> begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (

let uu____7833 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar uu____7833 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____7834 = (

let uu____7837 = (

let uu____7840 = (

let uu____7845 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (

let uu____7846 = (

let uu____7847 = (

let uu____7856 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7856))
in (uu____7847)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____7845 uu____7846)))
in (uu____7840 FStar_Pervasives_Native.None p))
in (FStar_Syntax_Util.b2t uu____7837))
in (FStar_Syntax_Util.refine x uu____7834)))
in (

let uu____7883 = (

let uu___374_7884 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = uu___374_7884.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___374_7884.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder uu____7883)))))
end)
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (

let uu____7901 = (FStar_List.map (fun uu____7925 -> (match (uu____7925) with
| (x, uu____7939) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append uu____7901 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun uu____7998 -> (match (uu____7998) with
| (x, uu____8012) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let early_prims_inductive = ((

let uu____8022 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____8022)) && (FStar_List.existsb (fun s -> (Prims.op_Equality s tc.FStar_Ident.ident.FStar_Ident.idText)) early_prims_inductives))
in (

let discriminator_ses = (match ((Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) with
| true -> begin
[]
end
| uu____8030 -> begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = (early_prims_inductive || (

let uu____8035 = (

let uu____8036 = (FStar_TypeChecker_Env.current_module env)
in uu____8036.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8035)))
in (

let quals = (

let uu____8040 = (FStar_List.filter (fun uu___360_8044 -> (match (uu___360_8044) with
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
| uu____8045 -> begin
false
end)) iquals)
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::(match (only_decl) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Assumption)::[]
end
| uu____8048 -> begin
[]
end)) uu____8040))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (

let uu____8080 = (

let uu____8081 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8081))
in (FStar_Syntax_Syntax.mk_Total uu____8080))
in (

let uu____8082 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8082)))
in (

let decl = (

let uu____8086 = (FStar_Ident.range_of_lid discriminator_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____8086; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____8088 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8088) with
| true -> begin
(

let uu____8089 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" uu____8089))
end
| uu____8090 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8093 -> begin
(

let body = (match ((not (refine_domain))) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____8099 -> begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8140 -> (match (uu____8140) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((b && (j < ntps))) with
| true -> begin
(

let uu____8164 = (

let uu____8167 = (

let uu____8168 = (

let uu____8175 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8175), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8168))
in (pos uu____8167))
in ((uu____8164), (b)))
end
| uu____8180 -> begin
(

let uu____8181 = (

let uu____8184 = (

let uu____8185 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8185))
in (pos uu____8184))
in ((uu____8181), (b)))
end))
end))))
in (

let pat_true = (

let uu____8203 = (

let uu____8206 = (

let uu____8207 = (

let uu____8220 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8220), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8207))
in (pos uu____8206))
in ((uu____8203), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_true_bool)))
in (

let pat_false = (

let uu____8254 = (

let uu____8257 = (

let uu____8258 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8258))
in (pos uu____8257))
in ((uu____8254), (FStar_Pervasives_Native.None), (FStar_Syntax_Util.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst unrefined_arg_binder))
in (

let uu____8272 = (

let uu____8279 = (

let uu____8280 = (

let uu____8303 = (

let uu____8320 = (FStar_Syntax_Util.branch pat_true)
in (

let uu____8335 = (

let uu____8352 = (FStar_Syntax_Util.branch pat_false)
in (uu____8352)::[])
in (uu____8320)::uu____8335))
in ((arg_exp), (uu____8303)))
in FStar_Syntax_Syntax.Tm_match (uu____8280))
in (FStar_Syntax_Syntax.mk uu____8279))
in (uu____8272 FStar_Pervasives_Native.None p))))))
end)
in (

let dd = (

let uu____8431 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____8431) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____8434 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____8443 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____8445 = (

let uu____8450 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____8450))
in (

let uu____8451 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in (FStar_Syntax_Util.mk_letbinding uu____8445 uvs lbtyp FStar_Parser_Const.effect_Tot_lid uu____8451 [] FStar_Range.dummyRange)))
in (

let impl = (

let uu____8457 = (

let uu____8458 = (

let uu____8465 = (

let uu____8468 = (

let uu____8469 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____8469 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____8468)::[])
in ((((false), ((lb)::[]))), (uu____8465)))
in FStar_Syntax_Syntax.Sig_let (uu____8458))
in {FStar_Syntax_Syntax.sigel = uu____8457; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((

let uu____8481 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8481) with
| true -> begin
(

let uu____8482 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" uu____8482))
end
| uu____8483 -> begin
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

let subst1 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8552 -> (match (uu____8552) with
| (a, uu____8560) -> begin
(

let uu____8565 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (uu____8565) with
| (field_name, uu____8571) -> begin
(

let field_proj_tm = (

let uu____8573 = (

let uu____8574 = (FStar_Syntax_Syntax.lid_as_fv field_name (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____8574))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8573 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) FStar_Pervasives_Native.None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (

let uu____8599 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____8641 -> (match (uu____8641) with
| (x, uu____8651) -> begin
(

let p1 = (FStar_Syntax_Syntax.range_of_bv x)
in (

let uu____8657 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____8657) with
| (field_name, uu____8665) -> begin
(

let t = (

let uu____8669 = (

let uu____8670 = (

let uu____8673 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total uu____8673))
in (FStar_Syntax_Util.arrow binders uu____8670))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____8669))
in (

let only_decl = (early_prims_inductive || (

let uu____8678 = (

let uu____8679 = (FStar_TypeChecker_Env.current_module env)
in uu____8679.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____8678)))
in (

let no_decl = false
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____8695 = (FStar_List.filter (fun uu___361_8699 -> (match (uu___361_8699) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____8700 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____8695)
end
| uu____8701 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___362_8713 -> (match (uu___362_8713) with
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
| uu____8714 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let attrs = (match (only_decl) with
| true -> begin
[]
end
| uu____8720 -> begin
(FStar_Syntax_Util.attr_substitute)::[]
end)
in (

let decl = (

let uu____8722 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu____8722; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____8724 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____8724) with
| true -> begin
(

let uu____8725 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" uu____8725))
end
| uu____8726 -> begin
()
end));
(match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____8729 -> begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j uu____8771 -> (match (uu____8771) with
| (x1, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in (match ((Prims.op_Equality (i + ntps) j)) with
| true -> begin
(

let uu____8795 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((uu____8795), (b)))
end
| uu____8800 -> begin
(match ((b && (j < ntps))) with
| true -> begin
(

let uu____8811 = (

let uu____8814 = (

let uu____8815 = (

let uu____8822 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in ((uu____8822), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____8815))
in (pos uu____8814))
in ((uu____8811), (b)))
end
| uu____8827 -> begin
(

let uu____8828 = (

let uu____8831 = (

let uu____8832 = (FStar_Syntax_Syntax.gen_bv x1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (uu____8832))
in (pos uu____8831))
in ((uu____8828), (b)))
end)
end))
end))))
in (

let pat = (

let uu____8850 = (

let uu____8853 = (

let uu____8854 = (

let uu____8867 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (fvq)))
in ((uu____8867), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (uu____8854))
in (pos uu____8853))
in (

let uu____8876 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((uu____8850), (FStar_Pervasives_Native.None), (uu____8876))))
in (

let body = (

let uu____8892 = (

let uu____8899 = (

let uu____8900 = (

let uu____8923 = (

let uu____8940 = (FStar_Syntax_Util.branch pat)
in (uu____8940)::[])
in ((arg_exp), (uu____8923)))
in FStar_Syntax_Syntax.Tm_match (uu____8900))
in (FStar_Syntax_Syntax.mk uu____8899))
in (uu____8892 FStar_Pervasives_Native.None p1))
in (

let imp = (FStar_Syntax_Util.abs binders body FStar_Pervasives_Native.None)
in (

let dd = (

let uu____9008 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____9008) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____9011 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let lbtyp = (match (no_decl) with
| true -> begin
t
end
| uu____9017 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let lb = (

let uu____9019 = (

let uu____9024 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____9024))
in (

let uu____9025 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = uu____9019; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____9025; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange}))
in (

let impl = (

let uu____9031 = (

let uu____9032 = (

let uu____9039 = (

let uu____9042 = (

let uu____9043 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____9043 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____9042)::[])
in ((((false), ((lb)::[]))), (uu____9039)))
in FStar_Syntax_Syntax.Sig_let (uu____9032))
in {FStar_Syntax_Syntax.sigel = uu____9031; FStar_Syntax_Syntax.sigrng = p1; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in ((

let uu____9055 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes")))
in (match (uu____9055) with
| true -> begin
(

let uu____9056 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" uu____9056))
end
| uu____9057 -> begin
()
end));
(match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____9060 -> begin
(decl)::(impl)::[]
end);
))))))))))
end);
))))))))
end)))
end))))
in (FStar_All.pipe_right uu____8599 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses))))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, uu____9104) when (

let uu____9109 = (FStar_Ident.lid_equals constr_lid FStar_Parser_Const.lexcons_lid)
in (not (uu____9109))) -> begin
(

let uu____9110 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9110) with
| (univ_opening, uvs1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let uu____9132 = (FStar_Syntax_Util.arrow_formals t1)
in (match (uu____9132) with
| (formals, uu____9150) -> begin
(

let uu____9171 = (

let tps_opt = (FStar_Util.find_map tcs (fun se1 -> (

let uu____9203 = (

let uu____9204 = (

let uu____9205 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____9205))
in (FStar_Ident.lid_equals typ_lid uu____9204))
in (match (uu____9203) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9224, uvs', tps, typ0, uu____9228, constrs) -> begin
FStar_Pervasives_Native.Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1")))))
end
| uu____9245 -> begin
(failwith "Impossible")
end)
end
| uu____9254 -> begin
FStar_Pervasives_Native.None
end))))
in (match (tps_opt) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9286 = (FStar_Ident.lid_equals typ_lid FStar_Parser_Const.exn_lid)
in (match (uu____9286) with
| true -> begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end
| uu____9299 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedDataConstructor), ("Unexpected data constructor")) se.FStar_Syntax_Syntax.sigrng)
end))
end))
in (match (uu____9171) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps1 = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ01 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let uu____9313 = (FStar_Syntax_Util.arrow_formals typ01)
in (match (uu____9313) with
| (indices, uu____9331) -> begin
(

let refine_domain = (

let uu____9353 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___363_9358 -> (match (uu___363_9358) with
| FStar_Syntax_Syntax.RecordConstructor (uu____9359) -> begin
true
end
| uu____9368 -> begin
false
end))))
in (match (uu____9353) with
| true -> begin
false
end
| uu____9369 -> begin
should_refine
end))
in (

let fv_qual = (

let filter_records = (fun uu___364_9378 -> (match (uu___364_9378) with
| FStar_Syntax_Syntax.RecordConstructor (uu____9381, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| uu____9393 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____9394 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____9394) with
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
| uu____9403 -> begin
iquals
end)
in (

let fields = (

let uu____9405 = (FStar_Util.first_N n_typars formals)
in (match (uu____9405) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun uu____9488 uu____9489 -> (match (((uu____9488), (uu____9489))) with
| ((x, uu____9515), (x', uu____9517)) -> begin
(

let uu____9538 = (

let uu____9545 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (uu____9545)))
in FStar_Syntax_Syntax.NT (uu____9538))
end)) imp_tps inductive_tps1)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals1 fv_qual refine_domain env typ_lid constr_lid uvs1 inductive_tps1 indices fields)))))
end))))
end))
end)))
end))
end
| uu____9550 -> begin
[]
end))




