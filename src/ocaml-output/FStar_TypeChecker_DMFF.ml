
open Prims
open FStar_Pervasives
type env =
{tcenv : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let __proj__Mkenv__item__tcenv : env  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; subst = subst1; tc_const = tc_const} -> begin
tcenv
end))


let __proj__Mkenv__item__subst : env  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; subst = subst1; tc_const = tc_const} -> begin
subst1
end))


let __proj__Mkenv__item__tc_const : env  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {tcenv = tcenv; subst = subst1; tc_const = tc_const} -> begin
tc_const
end))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {tcenv = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env wp_a)
in (

let a1 = (

let uu___28_129 = a
in (

let uu____130 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___28_129.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___28_129.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____130}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in ((

let uu____143 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____143) with
| true -> begin
((d "Elaborating extra WP combinators");
(

let uu____149 = (FStar_Syntax_Print.term_to_string wp_a1)
in (FStar_Util.print1 "wp_a is: %s\n" uu____149));
)
end
| uu____152 -> begin
()
end));
(

let rec collect_binders = (fun t -> (

let uu____168 = (

let uu____169 = (

let uu____172 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____172))
in uu____169.FStar_Syntax_Syntax.n)
in (match (uu____168) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uu____207) -> begin
t1
end
| uu____216 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (

let uu____218 = (collect_binders rest)
in (FStar_List.append bs uu____218)))
end
| FStar_Syntax_Syntax.Tm_type (uu____233) -> begin
[]
end
| uu____240 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let gamma = (

let uu____267 = (collect_binders wp_a1)
in (FStar_All.pipe_right uu____267 FStar_Syntax_Util.name_binders))
in ((

let uu____293 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____293) with
| true -> begin
(

let uu____297 = (

let uu____299 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" uu____299))
in (d uu____297))
end
| uu____303 -> begin
()
end));
(

let unknown = FStar_Syntax_Syntax.tun
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let register = (fun env1 lident def -> (

let uu____337 = (FStar_TypeChecker_Util.mk_toplevel_definition env1 lident def)
in (match (uu____337) with
| (sigelt, fv) -> begin
((

let uu____345 = (

let uu____348 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____348)
in (FStar_ST.op_Colon_Equals sigelts uu____345));
fv;
)
end)))
in (

let binders_of_list1 = (FStar_List.map (fun uu____428 -> (match (uu____428) with
| (t, b) -> begin
(

let uu____442 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (uu____442)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (

let uu____481 = (FStar_Syntax_Syntax.as_implicit true)
in (((FStar_Pervasives_Native.fst t)), (uu____481)))))
in (

let args_of_binders1 = (FStar_List.map (fun bv -> (

let uu____515 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst bv))
in (FStar_Syntax_Syntax.as_arg uu____515))))
in (

let uu____518 = (

let uu____535 = (

let mk2 = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let body = (

let uu____560 = (

let uu____563 = (FStar_Syntax_Syntax.bv_to_name t)
in (f uu____563))
in (FStar_Syntax_Util.arrow gamma uu____560))
in (

let uu____564 = (

let uu____565 = (

let uu____574 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____581 = (

let uu____590 = (FStar_Syntax_Syntax.mk_binder t)
in (uu____590)::[])
in (uu____574)::uu____581))
in (FStar_List.append binders uu____565))
in (FStar_Syntax_Util.abs uu____564 body FStar_Pervasives_Native.None)))))
in (

let uu____621 = (mk2 FStar_Syntax_Syntax.mk_Total)
in (

let uu____622 = (mk2 FStar_Syntax_Syntax.mk_GTotal)
in ((uu____621), (uu____622)))))
in (match (uu____535) with
| (ctx_def, gctx_def) -> begin
(

let ctx_lid = (mk_lid "ctx")
in (

let ctx_fv = (register env ctx_lid ctx_def)
in (

let gctx_lid = (mk_lid "gctx")
in (

let gctx_fv = (register env gctx_lid gctx_def)
in (

let mk_app1 = (fun fv t -> (

let uu____664 = (

let uu____665 = (

let uu____682 = (

let uu____693 = (FStar_List.map (fun uu____715 -> (match (uu____715) with
| (bv, uu____727) -> begin
(

let uu____732 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____733 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____732), (uu____733))))
end)) binders)
in (

let uu____735 = (

let uu____742 = (

let uu____747 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____748 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____747), (uu____748))))
in (

let uu____750 = (

let uu____757 = (

let uu____762 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (uu____762)))
in (uu____757)::[])
in (uu____742)::uu____750))
in (FStar_List.append uu____693 uu____735)))
in ((fv), (uu____682)))
in FStar_Syntax_Syntax.Tm_app (uu____665))
in (mk1 uu____664)))
in ((env), ((mk_app1 ctx_fv)), ((mk_app1 gctx_fv))))))))
end))
in (match (uu____518) with
| (env1, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let x = (

let uu____835 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None uu____835))
in (

let ret1 = (

let uu____840 = (

let uu____841 = (

let uu____844 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx uu____844))
in (FStar_Syntax_Util.residual_tot uu____841))
in FStar_Pervasives_Native.Some (uu____840))
in (

let body = (

let uu____848 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma uu____848 ret1))
in (

let uu____851 = (

let uu____852 = (mk_all_implicit binders)
in (

let uu____859 = (binders_of_list1 ((((a1), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append uu____852 uu____859)))
in (FStar_Syntax_Util.abs uu____851 body ret1))))))
in (

let c_pure1 = (

let uu____897 = (mk_lid "pure")
in (register env1 uu____897 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let l = (

let uu____907 = (

let uu____908 = (

let uu____909 = (

let uu____918 = (

let uu____925 = (

let uu____926 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____926))
in (FStar_Syntax_Syntax.mk_binder uu____925))
in (uu____918)::[])
in (

let uu____939 = (

let uu____942 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____942))
in (FStar_Syntax_Util.arrow uu____909 uu____939)))
in (mk_gctx uu____908))
in (FStar_Syntax_Syntax.gen_bv "l" FStar_Pervasives_Native.None uu____907))
in (

let r = (

let uu____945 = (

let uu____946 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____946))
in (FStar_Syntax_Syntax.gen_bv "r" FStar_Pervasives_Native.None uu____945))
in (

let ret1 = (

let uu____951 = (

let uu____952 = (

let uu____955 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____955))
in (FStar_Syntax_Util.residual_tot uu____952))
in FStar_Pervasives_Native.Some (uu____951))
in (

let outer_body = (

let gamma_as_args = (args_of_binders1 gamma)
in (

let inner_body = (

let uu____965 = (FStar_Syntax_Syntax.bv_to_name l)
in (

let uu____968 = (

let uu____979 = (

let uu____982 = (

let uu____983 = (

let uu____984 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app uu____984 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg uu____983))
in (uu____982)::[])
in (FStar_List.append gamma_as_args uu____979))
in (FStar_Syntax_Util.mk_app uu____965 uu____968)))
in (FStar_Syntax_Util.abs gamma inner_body ret1)))
in (

let uu____987 = (

let uu____988 = (mk_all_implicit binders)
in (

let uu____995 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append uu____988 uu____995)))
in (FStar_Syntax_Util.abs uu____987 outer_body ret1))))))))
in (

let c_app1 = (

let uu____1047 = (mk_lid "app")
in (register env1 uu____1047 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1059 = (

let uu____1068 = (

let uu____1075 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1075))
in (uu____1068)::[])
in (

let uu____1088 = (

let uu____1091 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____1091))
in (FStar_Syntax_Util.arrow uu____1059 uu____1088)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____1095 = (

let uu____1096 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____1096))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____1095))
in (

let ret1 = (

let uu____1101 = (

let uu____1102 = (

let uu____1105 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1105))
in (FStar_Syntax_Util.residual_tot uu____1102))
in FStar_Pervasives_Native.Some (uu____1101))
in (

let uu____1106 = (

let uu____1107 = (mk_all_implicit binders)
in (

let uu____1114 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a11), (false)))::[]))
in (FStar_List.append uu____1107 uu____1114)))
in (

let uu____1165 = (

let uu____1168 = (

let uu____1179 = (

let uu____1182 = (

let uu____1183 = (

let uu____1194 = (

let uu____1197 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1197)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1194))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1183))
in (

let uu____1206 = (

let uu____1209 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1209)::[])
in (uu____1182)::uu____1206))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1179))
in (FStar_Syntax_Util.mk_app c_app1 uu____1168))
in (FStar_Syntax_Util.abs uu____1106 uu____1165 ret1)))))))))
in (

let c_lift11 = (

let uu____1219 = (mk_lid "lift1")
in (register env1 uu____1219 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1233 = (

let uu____1242 = (

let uu____1249 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1249))
in (

let uu____1250 = (

let uu____1259 = (

let uu____1266 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder uu____1266))
in (uu____1259)::[])
in (uu____1242)::uu____1250))
in (

let uu____1285 = (

let uu____1288 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal uu____1288))
in (FStar_Syntax_Util.arrow uu____1233 uu____1285)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____1292 = (

let uu____1293 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____1293))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____1292))
in (

let a2 = (

let uu____1296 = (

let uu____1297 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1297))
in (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None uu____1296))
in (

let ret1 = (

let uu____1302 = (

let uu____1303 = (

let uu____1306 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx uu____1306))
in (FStar_Syntax_Util.residual_tot uu____1303))
in FStar_Pervasives_Native.Some (uu____1302))
in (

let uu____1307 = (

let uu____1308 = (mk_all_implicit binders)
in (

let uu____1315 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a11), (false)))::(((a2), (false)))::[]))
in (FStar_List.append uu____1308 uu____1315)))
in (

let uu____1380 = (

let uu____1383 = (

let uu____1394 = (

let uu____1397 = (

let uu____1398 = (

let uu____1409 = (

let uu____1412 = (

let uu____1413 = (

let uu____1424 = (

let uu____1427 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1427)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1424))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1413))
in (

let uu____1436 = (

let uu____1439 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1439)::[])
in (uu____1412)::uu____1436))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1409))
in (FStar_Syntax_Util.mk_app c_app1 uu____1398))
in (

let uu____1448 = (

let uu____1451 = (FStar_Syntax_Syntax.bv_to_name a2)
in (uu____1451)::[])
in (uu____1397)::uu____1448))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1394))
in (FStar_Syntax_Util.mk_app c_app1 uu____1383))
in (FStar_Syntax_Util.abs uu____1307 uu____1380 ret1)))))))))))
in (

let c_lift21 = (

let uu____1461 = (mk_lid "lift2")
in (register env1 uu____1461 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1473 = (

let uu____1482 = (

let uu____1489 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1489))
in (uu____1482)::[])
in (

let uu____1502 = (

let uu____1505 = (

let uu____1506 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1506))
in (FStar_Syntax_Syntax.mk_Total uu____1505))
in (FStar_Syntax_Util.arrow uu____1473 uu____1502)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let ret1 = (

let uu____1512 = (

let uu____1513 = (

let uu____1516 = (

let uu____1517 = (

let uu____1526 = (

let uu____1533 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1533))
in (uu____1526)::[])
in (

let uu____1546 = (

let uu____1549 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____1549))
in (FStar_Syntax_Util.arrow uu____1517 uu____1546)))
in (mk_ctx uu____1516))
in (FStar_Syntax_Util.residual_tot uu____1513))
in FStar_Pervasives_Native.Some (uu____1512))
in (

let e1 = (

let uu____1551 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" FStar_Pervasives_Native.None uu____1551))
in (

let body = (

let uu____1556 = (

let uu____1557 = (

let uu____1566 = (FStar_Syntax_Syntax.mk_binder e1)
in (uu____1566)::[])
in (FStar_List.append gamma uu____1557))
in (

let uu____1591 = (

let uu____1594 = (FStar_Syntax_Syntax.bv_to_name f)
in (

let uu____1597 = (

let uu____1608 = (

let uu____1609 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg uu____1609))
in (

let uu____1610 = (args_of_binders1 gamma)
in (uu____1608)::uu____1610))
in (FStar_Syntax_Util.mk_app uu____1594 uu____1597)))
in (FStar_Syntax_Util.abs uu____1556 uu____1591 ret1)))
in (

let uu____1613 = (

let uu____1614 = (mk_all_implicit binders)
in (

let uu____1621 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append uu____1614 uu____1621)))
in (FStar_Syntax_Util.abs uu____1613 body ret1)))))))))
in (

let c_push1 = (

let uu____1666 = (mk_lid "push")
in (register env1 uu____1666 c_push))
in (

let ret_tot_wp_a = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot wp_a1))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1693 = (

let uu____1694 = (

let uu____1711 = (args_of_binders1 binders)
in ((c), (uu____1711)))
in FStar_Syntax_Syntax.Tm_app (uu____1694))
in (mk1 uu____1693))
end
| uu____1734 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (

let uu____1740 = (

let uu____1741 = (

let uu____1750 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (

let uu____1757 = (

let uu____1766 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (uu____1766)::[])
in (uu____1750)::uu____1757))
in (

let uu____1791 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____1741 uu____1791)))
in (FStar_Syntax_Syntax.mk_Total uu____1740))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let uu____1796 = (

let uu____1797 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(c)::[]))
in (FStar_List.append binders uu____1797))
in (

let uu____1812 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____1817 = (

let uu____1820 = (

let uu____1831 = (

let uu____1834 = (

let uu____1835 = (

let uu____1846 = (

let uu____1855 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg uu____1855))
in (uu____1846)::[])
in (FStar_Syntax_Util.mk_app l_ite uu____1835))
in (uu____1834)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1831))
in (FStar_Syntax_Util.mk_app c_lift21 uu____1820))
in (FStar_Syntax_Util.ascribe uu____1817 ((FStar_Util.Inr (result_comp)), (FStar_Pervasives_Native.None)))))
in (FStar_Syntax_Util.abs uu____1796 uu____1812 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp result_comp))))))))
in (

let wp_if_then_else1 = (

let uu____1899 = (mk_lid "wp_if_then_else")
in (register env1 uu____1899 wp_if_then_else))
in (

let wp_if_then_else2 = (mk_generic_app wp_if_then_else1)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let body = (

let uu____1916 = (

let uu____1927 = (

let uu____1930 = (

let uu____1931 = (

let uu____1942 = (

let uu____1945 = (

let uu____1946 = (

let uu____1957 = (

let uu____1966 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1966))
in (uu____1957)::[])
in (FStar_Syntax_Util.mk_app l_and uu____1946))
in (uu____1945)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1942))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1931))
in (

let uu____1991 = (

let uu____1994 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1994)::[])
in (uu____1930)::uu____1991))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1927))
in (FStar_Syntax_Util.mk_app c_app1 uu____1916))
in (

let uu____2003 = (

let uu____2004 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____2004))
in (FStar_Syntax_Util.abs uu____2003 body ret_tot_wp_a))))))
in (

let wp_assert1 = (

let uu____2020 = (mk_lid "wp_assert")
in (register env1 uu____2020 wp_assert))
in (

let wp_assert2 = (mk_generic_app wp_assert1)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let body = (

let uu____2037 = (

let uu____2048 = (

let uu____2051 = (

let uu____2052 = (

let uu____2063 = (

let uu____2066 = (

let uu____2067 = (

let uu____2078 = (

let uu____2087 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____2087))
in (uu____2078)::[])
in (FStar_Syntax_Util.mk_app l_imp uu____2067))
in (uu____2066)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2063))
in (FStar_Syntax_Util.mk_app c_pure1 uu____2052))
in (

let uu____2112 = (

let uu____2115 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____2115)::[])
in (uu____2051)::uu____2112))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2048))
in (FStar_Syntax_Util.mk_app c_app1 uu____2037))
in (

let uu____2124 = (

let uu____2125 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____2125))
in (FStar_Syntax_Util.abs uu____2124 body ret_tot_wp_a))))))
in (

let wp_assume1 = (

let uu____2141 = (mk_lid "wp_assume")
in (register env1 uu____2141 wp_assume))
in (

let wp_assume2 = (mk_generic_app wp_assume1)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____2154 = (

let uu____2163 = (

let uu____2170 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____2170))
in (uu____2163)::[])
in (

let uu____2183 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____2154 uu____2183)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let body = (

let uu____2191 = (

let uu____2202 = (

let uu____2205 = (

let uu____2206 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure1 uu____2206))
in (

let uu____2225 = (

let uu____2228 = (

let uu____2229 = (

let uu____2240 = (

let uu____2243 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____2243)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2240))
in (FStar_Syntax_Util.mk_app c_push1 uu____2229))
in (uu____2228)::[])
in (uu____2205)::uu____2225))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2202))
in (FStar_Syntax_Util.mk_app c_app1 uu____2191))
in (

let uu____2260 = (

let uu____2261 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(b)::(f)::[]))
in (FStar_List.append binders uu____2261))
in (FStar_Syntax_Util.abs uu____2260 body ret_tot_wp_a))))))
in (

let wp_close1 = (

let uu____2277 = (mk_lid "wp_close")
in (register env1 uu____2277 wp_close))
in (

let wp_close2 = (mk_generic_app wp_close1)
in (

let ret_tot_type = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype))
in (

let ret_gtot_type = (

let uu____2288 = (

let uu____2289 = (

let uu____2290 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____2290))
in (FStar_Syntax_Util.residual_comp_of_lcomp uu____2289))
in FStar_Pervasives_Native.Some (uu____2288))
in (

let mk_forall1 = (fun x body -> (

let uu____2302 = (

let uu____2309 = (

let uu____2310 = (

let uu____2327 = (

let uu____2338 = (

let uu____2347 = (

let uu____2348 = (

let uu____2349 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2349)::[])
in (FStar_Syntax_Util.abs uu____2348 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg uu____2347))
in (uu____2338)::[])
in ((FStar_Syntax_Util.tforall), (uu____2327)))
in FStar_Syntax_Syntax.Tm_app (uu____2310))
in (FStar_Syntax_Syntax.mk uu____2309))
in (uu____2302 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (

let uu____2407 = (

let uu____2408 = (FStar_Syntax_Subst.compress t)
in uu____2408.FStar_Syntax_Syntax.n)
in (match (uu____2407) with
| FStar_Syntax_Syntax.Tm_type (uu____2412) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2445 -> (match (uu____2445) with
| (b, uu____2454) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____2459 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____2472 = (

let uu____2473 = (FStar_Syntax_Subst.compress t)
in uu____2473.FStar_Syntax_Syntax.n)
in (match (uu____2472) with
| FStar_Syntax_Syntax.Tm_type (uu____2477) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2510 -> (match (uu____2510) with
| (b, uu____2519) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____2524 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel1 = (mk_rel rel)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t)
in (

let uu____2598 = (

let uu____2599 = (FStar_Syntax_Subst.compress t1)
in uu____2599.FStar_Syntax_Syntax.n)
in (match (uu____2598) with
| FStar_Syntax_Syntax.Tm_type (uu____2604) -> begin
(rel x y)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____2607); FStar_Syntax_Syntax.pos = uu____2608; FStar_Syntax_Syntax.vars = uu____2609}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2653 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2653) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2663 = (

let uu____2666 = (

let uu____2677 = (

let uu____2686 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2686))
in (uu____2677)::[])
in (FStar_Syntax_Util.mk_app x uu____2666))
in (

let uu____2703 = (

let uu____2706 = (

let uu____2717 = (

let uu____2726 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2726))
in (uu____2717)::[])
in (FStar_Syntax_Util.mk_app y uu____2706))
in (mk_rel1 b uu____2663 uu____2703)))
in (mk_forall1 a11 body)))
end
| uu____2743 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2750 = (

let uu____2753 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2756 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2753 uu____2756)))
in (

let uu____2759 = (

let uu____2762 = (

let uu____2765 = (

let uu____2776 = (

let uu____2785 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2785))
in (uu____2776)::[])
in (FStar_Syntax_Util.mk_app x uu____2765))
in (

let uu____2802 = (

let uu____2805 = (

let uu____2816 = (

let uu____2825 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____2825))
in (uu____2816)::[])
in (FStar_Syntax_Util.mk_app y uu____2805))
in (mk_rel1 b uu____2762 uu____2802)))
in (FStar_Syntax_Util.mk_imp uu____2750 uu____2759)))
in (

let uu____2842 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____2842)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____2845); FStar_Syntax_Syntax.pos = uu____2846; FStar_Syntax_Syntax.vars = uu____2847}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2891 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2891) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2901 = (

let uu____2904 = (

let uu____2915 = (

let uu____2924 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2924))
in (uu____2915)::[])
in (FStar_Syntax_Util.mk_app x uu____2904))
in (

let uu____2941 = (

let uu____2944 = (

let uu____2955 = (

let uu____2964 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2964))
in (uu____2955)::[])
in (FStar_Syntax_Util.mk_app y uu____2944))
in (mk_rel1 b uu____2901 uu____2941)))
in (mk_forall1 a11 body)))
end
| uu____2981 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2988 = (

let uu____2991 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2994 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2991 uu____2994)))
in (

let uu____2997 = (

let uu____3000 = (

let uu____3003 = (

let uu____3014 = (

let uu____3023 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____3023))
in (uu____3014)::[])
in (FStar_Syntax_Util.mk_app x uu____3003))
in (

let uu____3040 = (

let uu____3043 = (

let uu____3054 = (

let uu____3063 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____3063))
in (uu____3054)::[])
in (FStar_Syntax_Util.mk_app y uu____3043))
in (mk_rel1 b uu____3000 uu____3040)))
in (FStar_Syntax_Util.mk_imp uu____2988 uu____2997)))
in (

let uu____3080 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____3080)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders1, comp) -> begin
(

let t2 = (

let uu___242_3119 = t1
in (

let uu____3120 = (

let uu____3121 = (

let uu____3136 = (

let uu____3139 = (FStar_Syntax_Util.arrow binders1 comp)
in (FStar_Syntax_Syntax.mk_Total uu____3139))
in (((binder)::[]), (uu____3136)))
in FStar_Syntax_Syntax.Tm_arrow (uu____3121))
in {FStar_Syntax_Syntax.n = uu____3120; FStar_Syntax_Syntax.pos = uu___242_3119.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___242_3119.FStar_Syntax_Syntax.vars}))
in (mk_rel1 t2 x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3162) -> begin
(failwith "unhandled arrow")
end
| uu____3180 -> begin
(FStar_Syntax_Util.mk_untyped_eq2 x y)
end)))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" FStar_Pervasives_Native.None wp_a1)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" FStar_Pervasives_Native.None wp_a1)
in (

let rec mk_stronger = (fun t x y -> (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t)
in (

let uu____3217 = (

let uu____3218 = (FStar_Syntax_Subst.compress t1)
in uu____3218.FStar_Syntax_Syntax.n)
in (match (uu____3217) with
| FStar_Syntax_Syntax.Tm_type (uu____3221) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when (

let uu____3248 = (FStar_Syntax_Subst.compress head1)
in (FStar_Syntax_Util.is_tuple_constructor uu____3248)) -> begin
(

let project = (fun i tuple -> (

let projector = (

let uu____3269 = (

let uu____3270 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env1 uu____3270 i))
in (FStar_Syntax_Syntax.fvar uu____3269 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (FStar_Pervasives_Native.None)))::[]))))
in (

let uu____3300 = (

let uu____3311 = (FStar_List.mapi (fun i uu____3329 -> (match (uu____3329) with
| (t2, q) -> begin
(

let uu____3349 = (project i x)
in (

let uu____3352 = (project i y)
in (mk_stronger t2 uu____3349 uu____3352)))
end)) args)
in (match (uu____3311) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____3300) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____3406); FStar_Syntax_Syntax.pos = uu____3407; FStar_Syntax_Syntax.vars = uu____3408}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____3452 -> (match (uu____3452) with
| (bv, q) -> begin
(

let uu____3466 = (

let uu____3468 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "a" uu____3468))
in (FStar_Syntax_Syntax.gen_bv uu____3466 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____3477 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____3477))) bvs)
in (

let body = (

let uu____3479 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____3482 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____3479 uu____3482)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____3491); FStar_Syntax_Syntax.pos = uu____3492; FStar_Syntax_Syntax.vars = uu____3493}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____3537 -> (match (uu____3537) with
| (bv, q) -> begin
(

let uu____3551 = (

let uu____3553 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "a" uu____3553))
in (FStar_Syntax_Syntax.gen_bv uu____3551 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____3562 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____3562))) bvs)
in (

let body = (

let uu____3564 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____3567 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____3564 uu____3567)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| uu____3574 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (

let uu____3577 = (FStar_Syntax_Util.unascribe wp_a1)
in (

let uu____3580 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (

let uu____3583 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger uu____3577 uu____3580 uu____3583))))
in (

let uu____3586 = (

let uu____3587 = (binders_of_list1 ((((a1), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders uu____3587))
in (FStar_Syntax_Util.abs uu____3586 body ret_tot_type))))))
in (

let stronger1 = (

let uu____3629 = (mk_lid "stronger")
in (register env1 uu____3629 stronger))
in (

let stronger2 = (mk_generic_app stronger1)
in (

let ite_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3637 = (FStar_Util.prefix gamma)
in (match (uu____3637) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv1 = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq1 = (

let uu____3703 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm uu____3703))
in (

let uu____3708 = (FStar_Syntax_Util.destruct_typ_as_formula eq1)
in (match (uu____3708) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (binders1, [], body)) -> begin
(

let k_app = (

let uu____3718 = (args_of_binders1 binders1)
in (FStar_Syntax_Util.mk_app k_tm uu____3718))
in (

let guard_free1 = (

let uu____3730 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.guard_free FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3730))
in (

let pat = (

let uu____3734 = (

let uu____3745 = (FStar_Syntax_Syntax.as_arg k_app)
in (uu____3745)::[])
in (FStar_Syntax_Util.mk_app guard_free1 uu____3734))
in (

let pattern_guarded_body = (

let uu____3773 = (

let uu____3774 = (

let uu____3781 = (

let uu____3782 = (

let uu____3803 = (FStar_Syntax_Syntax.binders_to_names binders1)
in (

let uu____3808 = (

let uu____3821 = (

let uu____3832 = (FStar_Syntax_Syntax.as_arg pat)
in (uu____3832)::[])
in (uu____3821)::[])
in ((uu____3803), (uu____3808))))
in FStar_Syntax_Syntax.Meta_pattern (uu____3782))
in ((body), (uu____3781)))
in FStar_Syntax_Syntax.Tm_meta (uu____3774))
in (mk1 uu____3773))
in (FStar_Syntax_Util.close_forall_no_univs binders1 pattern_guarded_body)))))
end
| uu____3895 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (

let uu____3904 = (

let uu____3907 = (

let uu____3908 = (

let uu____3911 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____3914 = (

let uu____3925 = (args_of_binders1 wp_args)
in (

let uu____3928 = (

let uu____3931 = (

let uu____3932 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg uu____3932))
in (uu____3931)::[])
in (FStar_List.append uu____3925 uu____3928)))
in (FStar_Syntax_Util.mk_app uu____3911 uu____3914)))
in (FStar_Syntax_Util.mk_imp equiv1 uu____3908))
in (FStar_Syntax_Util.mk_forall_no_univ k uu____3907))
in (FStar_Syntax_Util.abs gamma uu____3904 ret_gtot_type))
in (

let uu____3933 = (

let uu____3934 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____3934))
in (FStar_Syntax_Util.abs uu____3933 body ret_gtot_type)))))
end)))
in (

let ite_wp1 = (

let uu____3950 = (mk_lid "ite_wp")
in (register env1 uu____3950 ite_wp))
in (

let ite_wp2 = (mk_generic_app ite_wp1)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3958 = (FStar_Util.prefix gamma)
in (match (uu____3958) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let body = (

let uu____4016 = (

let uu____4017 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (

let uu____4024 = (

let uu____4035 = (

let uu____4044 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____4044))
in (uu____4035)::[])
in (FStar_Syntax_Util.mk_app uu____4017 uu____4024)))
in (FStar_Syntax_Util.mk_forall_no_univ x uu____4016))
in (

let uu____4061 = (

let uu____4062 = (

let uu____4071 = (FStar_Syntax_Syntax.binders_of_list ((a1)::[]))
in (FStar_List.append uu____4071 gamma))
in (FStar_List.append binders uu____4062))
in (FStar_Syntax_Util.abs uu____4061 body ret_gtot_type))))
end)))
in (

let null_wp1 = (

let uu____4093 = (mk_lid "null_wp")
in (register env1 uu____4093 null_wp))
in (

let null_wp2 = (mk_generic_app null_wp1)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let body = (

let uu____4106 = (

let uu____4117 = (

let uu____4120 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____4121 = (

let uu____4124 = (

let uu____4125 = (

let uu____4136 = (

let uu____4145 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____4145))
in (uu____4136)::[])
in (FStar_Syntax_Util.mk_app null_wp2 uu____4125))
in (

let uu____4162 = (

let uu____4165 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____4165)::[])
in (uu____4124)::uu____4162))
in (uu____4120)::uu____4121))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____4117))
in (FStar_Syntax_Util.mk_app stronger2 uu____4106))
in (

let uu____4174 = (

let uu____4175 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____4175))
in (FStar_Syntax_Util.abs uu____4174 body ret_tot_type))))
in (

let wp_trivial1 = (

let uu____4191 = (mk_lid "wp_trivial")
in (register env1 uu____4191 wp_trivial))
in (

let wp_trivial2 = (mk_generic_app wp_trivial1)
in ((

let uu____4197 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____4197) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____4202 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (

let uu____4209 = (

let uu____4210 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____4210))
in (

let uu____4236 = (

let uu___349_4237 = ed
in (

let uu____4238 = (

let uu____4239 = (c wp_if_then_else2)
in (([]), (uu____4239)))
in (

let uu____4246 = (

let uu____4247 = (c ite_wp2)
in (([]), (uu____4247)))
in (

let uu____4254 = (

let uu____4255 = (c stronger2)
in (([]), (uu____4255)))
in (

let uu____4262 = (

let uu____4263 = (c wp_close2)
in (([]), (uu____4263)))
in (

let uu____4270 = (

let uu____4271 = (c wp_assert2)
in (([]), (uu____4271)))
in (

let uu____4278 = (

let uu____4279 = (c wp_assume2)
in (([]), (uu____4279)))
in (

let uu____4286 = (

let uu____4287 = (c null_wp2)
in (([]), (uu____4287)))
in (

let uu____4294 = (

let uu____4295 = (c wp_trivial2)
in (([]), (uu____4295)))
in {FStar_Syntax_Syntax.cattributes = uu___349_4237.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___349_4237.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___349_4237.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___349_4237.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___349_4237.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___349_4237.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___349_4237.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu____4238; FStar_Syntax_Syntax.ite_wp = uu____4246; FStar_Syntax_Syntax.stronger = uu____4254; FStar_Syntax_Syntax.close_wp = uu____4262; FStar_Syntax_Syntax.assert_p = uu____4270; FStar_Syntax_Syntax.assume_p = uu____4278; FStar_Syntax_Syntax.null_wp = uu____4286; FStar_Syntax_Syntax.trivial = uu____4294; FStar_Syntax_Syntax.repr = uu___349_4237.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___349_4237.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___349_4237.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___349_4237.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___349_4237.FStar_Syntax_Syntax.eff_attrs})))))))))
in ((uu____4209), (uu____4236)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.tcenv)


let set_env : env  ->  FStar_TypeChecker_Env.env  ->  env = (fun dmff_env env' -> (

let uu___354_4319 = dmff_env
in {tcenv = env'; subst = uu___354_4319.subst; tc_const = uu___354_4319.tc_const}))

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____4340 -> begin
false
end))


let __proj__N__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| N (_0) -> begin
_0
end))


let uu___is_M : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| M (_0) -> begin
true
end
| uu____4359 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  nm = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____4379) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c1) when (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___0_4393 -> (match (uu___0_4393) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____4396 -> begin
false
end)))) -> begin
M (c1.FStar_Syntax_Syntax.result_typ)
end
| uu____4398 -> begin
(

let uu____4399 = (

let uu____4405 = (

let uu____4407 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s" uu____4407))
in ((FStar_Errors.Error_UnexpectedDM4FType), (uu____4405)))
in (FStar_Errors.raise_error uu____4399 c.FStar_Syntax_Syntax.pos))
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___1_4417 -> (match (uu___1_4417) with
| N (t) -> begin
(

let uu____4420 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" uu____4420))
end
| M (t) -> begin
(

let uu____4424 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" uu____4424))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n1 -> (match (n1) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4433, c) -> begin
(nm_of_comp c)
end
| uu____4455 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (

let uu____4468 = (nm_of_comp c)
in (match (uu____4468) with
| M (uu____4470) -> begin
true
end
| N (uu____4472) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____4483 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ1 -> (

let uu____4499 = (

let uu____4508 = (

let uu____4515 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4515))
in (uu____4508)::[])
in (

let uu____4534 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4499 uu____4534))))
in (

let uu____4537 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once uu____4537))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun mk1 env a -> (

let uu____4579 = (

let uu____4580 = (

let uu____4595 = (

let uu____4604 = (

let uu____4611 = (

let uu____4612 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv uu____4612))
in (

let uu____4613 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4611), (uu____4613))))
in (uu____4604)::[])
in (

let uu____4631 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____4595), (uu____4631))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4580))
in (mk1 uu____4579)))
and star_type' : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type1 = (mk_star_to_type mk1)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____4671) -> begin
(

let binders1 = (FStar_List.map (fun uu____4717 -> (match (uu____4717) with
| (bv, aqual) -> begin
(

let uu____4736 = (

let uu___404_4737 = bv
in (

let uu____4738 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___404_4737.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___404_4737.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4738}))
in ((uu____4736), (aqual)))
end)) binders)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4743, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____4745); FStar_Syntax_Syntax.pos = uu____4746; FStar_Syntax_Syntax.vars = uu____4747}) -> begin
(

let uu____4776 = (

let uu____4777 = (

let uu____4792 = (

let uu____4795 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal uu____4795))
in ((binders1), (uu____4792)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4777))
in (mk1 uu____4776))
end
| uu____4806 -> begin
(

let uu____4807 = (is_monadic_arrow t1.FStar_Syntax_Syntax.n)
in (match (uu____4807) with
| N (hn) -> begin
(

let uu____4809 = (

let uu____4810 = (

let uu____4825 = (

let uu____4828 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total uu____4828))
in ((binders1), (uu____4825)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4810))
in (mk1 uu____4809))
end
| M (a) -> begin
(

let uu____4840 = (

let uu____4841 = (

let uu____4856 = (

let uu____4865 = (

let uu____4874 = (

let uu____4881 = (

let uu____4882 = (mk_star_to_type1 env a)
in (FStar_Syntax_Syntax.null_bv uu____4882))
in (

let uu____4883 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4881), (uu____4883))))
in (uu____4874)::[])
in (FStar_List.append binders1 uu____4865))
in (

let uu____4907 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____4856), (uu____4907))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4841))
in (mk1 uu____4840))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let debug1 = (fun t2 s -> (

let string_of_set = (fun f s1 -> (

let elts = (FStar_Util.set_elements s1)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(

let uu____5001 = (f x)
in (FStar_Util.string_builder_append strb uu____5001));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____5010 = (f x1)
in (FStar_Util.string_builder_append strb uu____5010));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (

let uu____5014 = (

let uu____5020 = (

let uu____5022 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____5024 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.format2 "Dependency found in term %s : %s" uu____5022 uu____5024)))
in ((FStar_Errors.Warning_DependencyFound), (uu____5020)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5014))))
in (

let rec is_non_dependent_arrow = (fun ty n1 -> (

let uu____5046 = (

let uu____5047 = (FStar_Syntax_Subst.compress ty)
in uu____5047.FStar_Syntax_Syntax.n)
in (match (uu____5046) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5073 = (

let uu____5075 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (not (uu____5075)))
in (match (uu____5073) with
| true -> begin
false
end
| uu____5080 -> begin
(FStar_All.try_with (fun uu___453_5092 -> (match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty1 -> (

let sinter = (

let uu____5116 = (FStar_Syntax_Free.names ty1)
in (FStar_Util.set_intersect uu____5116 s))
in (

let uu____5119 = (

let uu____5121 = (FStar_Util.set_is_empty sinter)
in (not (uu____5121)))
in (match (uu____5119) with
| true -> begin
((debug1 ty1 sinter);
(FStar_Exn.raise Not_found);
)
end
| uu____5125 -> begin
()
end))))
in (

let uu____5127 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5127) with
| (binders1, c1) -> begin
(

let s = (FStar_List.fold_left (fun s uu____5152 -> (match (uu____5152) with
| (bv, uu____5164) -> begin
((non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort);
(FStar_Util.set_add bv s);
)
end)) FStar_Syntax_Syntax.no_names binders1)
in (

let ct = (FStar_Syntax_Util.comp_result c1)
in ((non_dependent_or_raise s ct);
(

let k = (n1 - (FStar_List.length binders1))
in (match ((k > (Prims.parse_int "0"))) with
| true -> begin
(is_non_dependent_arrow ct k)
end
| uu____5185 -> begin
true
end));
)))
end)))
end)) (fun uu___452_5189 -> (match (uu___452_5189) with
| Not_found -> begin
false
end)))
end))
end
| uu____5192 -> begin
((

let uu____5194 = (

let uu____5200 = (

let uu____5202 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format1 "Not a dependent arrow : %s" uu____5202))
in ((FStar_Errors.Warning_NotDependentArrow), (uu____5200)))
in (FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos uu____5194));
false;
)
end)))
in (

let rec is_valid_application = (fun head2 -> (

let uu____5218 = (

let uu____5219 = (FStar_Syntax_Subst.compress head2)
in uu____5219.FStar_Syntax_Syntax.n)
in (match (uu____5218) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (

let uu____5225 = (FStar_Syntax_Subst.compress head2)
in (FStar_Syntax_Util.is_tuple_constructor uu____5225))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5228 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5228) with
| ((uu____5238, ty), uu____5240) -> begin
(

let uu____5245 = (is_non_dependent_arrow ty (FStar_List.length args))
in (match (uu____5245) with
| true -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env.tcenv t1)
in (

let uu____5258 = (

let uu____5259 = (FStar_Syntax_Subst.compress res)
in uu____5259.FStar_Syntax_Syntax.n)
in (match (uu____5258) with
| FStar_Syntax_Syntax.Tm_app (uu____5263) -> begin
true
end
| uu____5281 -> begin
((

let uu____5283 = (

let uu____5289 = (

let uu____5291 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format1 "Got a term which might be a non-dependent user-defined data-type %s\n" uu____5291))
in ((FStar_Errors.Warning_NondependentUserDefinedDataType), (uu____5289)))
in (FStar_Errors.log_issue head2.FStar_Syntax_Syntax.pos uu____5283));
false;
)
end)))
end
| uu____5296 -> begin
false
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5299) -> begin
true
end
| FStar_Syntax_Syntax.Tm_name (uu____5301) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5304) -> begin
(is_valid_application t2)
end
| uu____5309 -> begin
false
end)))
in (

let uu____5311 = (is_valid_application head1)
in (match (uu____5311) with
| true -> begin
(

let uu____5314 = (

let uu____5315 = (

let uu____5332 = (FStar_List.map (fun uu____5361 -> (match (uu____5361) with
| (t2, qual) -> begin
(

let uu____5386 = (star_type' env t2)
in ((uu____5386), (qual)))
end)) args)
in ((head1), (uu____5332)))
in FStar_Syntax_Syntax.Tm_app (uu____5315))
in (mk1 uu____5314))
end
| uu____5401 -> begin
(

let uu____5403 = (

let uu____5409 = (

let uu____5411 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" uu____5411))
in ((FStar_Errors.Fatal_WrongTerm), (uu____5409)))
in (FStar_Errors.raise_err uu____5403))
end)))))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5415) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____5416) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____5417) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5418) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____5446 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____5446) with
| (binders1, repr1) -> begin
(

let env1 = (

let uu___525_5454 = env
in (

let uu____5455 = (FStar_TypeChecker_Env.push_binders env.tcenv binders1)
in {tcenv = uu____5455; subst = uu___525_5454.subst; tc_const = uu___525_5454.tc_const}))
in (

let repr2 = (star_type' env1 repr1)
in (FStar_Syntax_Util.abs binders1 repr2 something)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, t2) when false -> begin
(

let x1 = (FStar_Syntax_Syntax.freshen_bv x)
in (

let sort = (star_type' env x1.FStar_Syntax_Syntax.sort)
in (

let subst1 = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x1))))::[]
in (

let t3 = (FStar_Syntax_Subst.subst subst1 t2)
in (

let t4 = (star_type' env t3)
in (

let subst2 = (FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::[]
in (

let t5 = (FStar_Syntax_Subst.subst subst2 t4)
in (mk1 (FStar_Syntax_Syntax.Tm_refine ((((

let uu___540_5482 = x1
in {FStar_Syntax_Syntax.ppname = uu___540_5482.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___540_5482.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t5))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____5489 = (

let uu____5490 = (

let uu____5497 = (star_type' env t2)
in ((uu____5497), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____5490))
in (mk1 uu____5489))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inl (t2), FStar_Pervasives_Native.None), something) -> begin
(

let uu____5549 = (

let uu____5550 = (

let uu____5577 = (star_type' env e)
in (

let uu____5580 = (

let uu____5597 = (

let uu____5606 = (star_type' env t2)
in FStar_Util.Inl (uu____5606))
in ((uu____5597), (FStar_Pervasives_Native.None)))
in ((uu____5577), (uu____5580), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5550))
in (mk1 uu____5549))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), FStar_Pervasives_Native.None), something) -> begin
(

let uu____5694 = (

let uu____5695 = (

let uu____5722 = (star_type' env e)
in (

let uu____5725 = (

let uu____5742 = (

let uu____5751 = (star_type' env (FStar_Syntax_Util.comp_result c))
in FStar_Util.Inl (uu____5751))
in ((uu____5742), (FStar_Pervasives_Native.None)))
in ((uu____5722), (uu____5725), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5695))
in (mk1 uu____5694))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5792, (uu____5793, FStar_Pervasives_Native.Some (uu____5794)), uu____5795) -> begin
(

let uu____5844 = (

let uu____5850 = (

let uu____5852 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Ascriptions with tactics are outside of the definition language: %s" uu____5852))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5850)))
in (FStar_Errors.raise_err uu____5844))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5856) -> begin
(

let uu____5863 = (

let uu____5869 = (

let uu____5871 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" uu____5871))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5869)))
in (FStar_Errors.raise_err uu____5863))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____5875) -> begin
(

let uu____5882 = (

let uu____5888 = (

let uu____5890 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" uu____5890))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5888)))
in (FStar_Errors.raise_err uu____5882))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5894) -> begin
(

let uu____5901 = (

let uu____5907 = (

let uu____5909 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_quoted is outside of the definition language: %s" uu____5909))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5907)))
in (FStar_Errors.raise_err uu____5901))
end
| FStar_Syntax_Syntax.Tm_constant (uu____5913) -> begin
(

let uu____5914 = (

let uu____5920 = (

let uu____5922 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" uu____5922))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5920)))
in (FStar_Errors.raise_err uu____5914))
end
| FStar_Syntax_Syntax.Tm_match (uu____5926) -> begin
(

let uu____5949 = (

let uu____5955 = (

let uu____5957 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" uu____5957))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5955)))
in (FStar_Errors.raise_err uu____5949))
end
| FStar_Syntax_Syntax.Tm_let (uu____5961) -> begin
(

let uu____5975 = (

let uu____5981 = (

let uu____5983 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" uu____5983))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5981)))
in (FStar_Errors.raise_err uu____5975))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5987) -> begin
(

let uu____6000 = (

let uu____6006 = (

let uu____6008 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" uu____6008))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____6006)))
in (FStar_Errors.raise_err uu____6000))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6012 = (

let uu____6018 = (

let uu____6020 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" uu____6020))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____6018)))
in (FStar_Errors.raise_err uu____6012))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6025 = (FStar_Syntax_Util.unfold_lazy i)
in (star_type' env uu____6025))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____6028) -> begin
(failwith "impossible")
end)))))


let is_monadic : FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___3_6060 -> (match (uu___3_6060) with
| FStar_Pervasives_Native.None -> begin
(failwith "un-annotated lambda?!")
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___2_6071 -> (match (uu___2_6071) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____6074 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____6084 = (

let uu____6085 = (FStar_Syntax_Subst.compress t)
in uu____6085.FStar_Syntax_Syntax.n)
in (match (uu____6084) with
| FStar_Syntax_Syntax.Tm_app (head1, args) when (FStar_Syntax_Util.is_tuple_constructor head1) -> begin
(

let r = (

let uu____6117 = (

let uu____6118 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____6118))
in (is_C uu____6117))
in (match (r) with
| true -> begin
((

let uu____6142 = (

let uu____6144 = (FStar_List.for_all (fun uu____6155 -> (match (uu____6155) with
| (h, uu____6164) -> begin
(is_C h)
end)) args)
in (not (uu____6144)))
in (match (uu____6142) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____6171 -> begin
()
end));
true;
)
end
| uu____6174 -> begin
((

let uu____6177 = (

let uu____6179 = (FStar_List.for_all (fun uu____6191 -> (match (uu____6191) with
| (h, uu____6200) -> begin
(

let uu____6205 = (is_C h)
in (not (uu____6205)))
end)) args)
in (not (uu____6179)))
in (match (uu____6177) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____6209 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____6234 = (nm_of_comp comp)
in (match (uu____6234) with
| M (t1) -> begin
((

let uu____6238 = (is_C t1)
in (match (uu____6238) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____6242 -> begin
()
end));
true;
)
end
| N (t1) -> begin
(is_C t1)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6247) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6253) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____6259, uu____6260) -> begin
(is_C t1)
end
| uu____6301 -> begin
false
end)))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env t e -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk1 env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" FStar_Pervasives_Native.None p_type)
in (

let body = (

let uu____6337 = (

let uu____6338 = (

let uu____6355 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____6358 = (

let uu____6369 = (

let uu____6378 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (uu____6378)))
in (uu____6369)::[])
in ((uu____6355), (uu____6358))))
in FStar_Syntax_Syntax.Tm_app (uu____6338))
in (mk1 uu____6337))
in (

let uu____6414 = (

let uu____6415 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____6415)::[])
in (FStar_Syntax_Util.abs uu____6414 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___4_6440 -> (match (uu___4_6440) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____6443 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let return_if = (fun uu____6681 -> (match (uu____6681) with
| (rec_nm, s_e, u_e) -> begin
(

let check1 = (fun t1 t2 -> (

let uu____6718 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (

let uu____6721 = (

let uu____6723 = (FStar_TypeChecker_Rel.teq env.tcenv t1 t2)
in (FStar_TypeChecker_Env.is_trivial uu____6723))
in (not (uu____6721))))
in (match (uu____6718) with
| true -> begin
(

let uu____6725 = (

let uu____6731 = (

let uu____6733 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6735 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6737 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" uu____6733 uu____6735 uu____6737))))
in ((FStar_Errors.Fatal_TypeMismatch), (uu____6731)))
in (FStar_Errors.raise_err uu____6725))
end
| uu____6741 -> begin
()
end)))
in (match (((rec_nm), (context_nm))) with
| (N (t1), N (t2)) -> begin
((check1 t1 t2);
((rec_nm), (s_e), (u_e));
)
end
| (M (t1), M (t2)) -> begin
((check1 t1 t2);
((rec_nm), (s_e), (u_e));
)
end
| (N (t1), M (t2)) -> begin
((check1 t1 t2);
(

let uu____6762 = (mk_return env t1 s_e)
in ((M (t1)), (uu____6762), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(

let uu____6769 = (

let uu____6775 = (

let uu____6777 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6779 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6781 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" uu____6777 uu____6779 uu____6781))))
in ((FStar_Errors.Fatal_EffectfulAndPureComputationMismatch), (uu____6775)))
in (FStar_Errors.raise_err uu____6769))
end))
end))
in (

let ensure_m = (fun env1 e2 -> (

let strip_m = (fun uu___5_6833 -> (match (uu___5_6833) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____6849 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(

let uu____6870 = (

let uu____6876 = (

let uu____6878 = (FStar_Syntax_Print.term_to_string t)
in (Prims.op_Hat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " uu____6878))
in ((FStar_Errors.Fatal_LetBoundMonadicMismatch), (uu____6876)))
in (FStar_Errors.raise_error uu____6870 e2.FStar_Syntax_Syntax.pos))
end
| M (uu____6888) -> begin
(

let uu____6889 = (check env1 e2 context_nm)
in (strip_m uu____6889))
end)))
in (

let uu____6896 = (

let uu____6897 = (FStar_Syntax_Subst.compress e)
in uu____6897.FStar_Syntax_Syntax.n)
in (match (uu____6896) with
| FStar_Syntax_Syntax.Tm_bvar (uu____6906) -> begin
(

let uu____6907 = (infer env e)
in (return_if uu____6907))
end
| FStar_Syntax_Syntax.Tm_name (uu____6914) -> begin
(

let uu____6915 = (infer env e)
in (return_if uu____6915))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6922) -> begin
(

let uu____6923 = (infer env e)
in (return_if uu____6923))
end
| FStar_Syntax_Syntax.Tm_abs (uu____6930) -> begin
(

let uu____6949 = (infer env e)
in (return_if uu____6949))
end
| FStar_Syntax_Syntax.Tm_constant (uu____6956) -> begin
(

let uu____6957 = (infer env e)
in (return_if uu____6957))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6964) -> begin
(

let uu____6971 = (infer env e)
in (return_if uu____6971))
end
| FStar_Syntax_Syntax.Tm_app (uu____6978) -> begin
(

let uu____6995 = (infer env e)
in (return_if uu____6995))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____7003 = (FStar_Syntax_Util.unfold_lazy i)
in (check env uu____7003 context_nm))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env1 e21 -> (check env1 e21 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env1 body -> (check env1 body context_nm)))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____7068) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____7074) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____7080, uu____7081) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____7122) -> begin
(

let uu____7136 = (

let uu____7138 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" uu____7138))
in (failwith uu____7136))
end
| FStar_Syntax_Syntax.Tm_type (uu____7147) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7155) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____7177) -> begin
(

let uu____7184 = (

let uu____7186 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" uu____7186))
in (failwith uu____7184))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7195) -> begin
(

let uu____7208 = (

let uu____7210 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" uu____7210))
in (failwith uu____7208))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____7219) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____7249 = (

let uu____7251 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" uu____7251))
in (failwith uu____7249))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let normalize1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::[]) env.tcenv)
in (

let uu____7281 = (

let uu____7282 = (FStar_Syntax_Subst.compress e)
in uu____7282.FStar_Syntax_Syntax.n)
in (match (uu____7281) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____7301 = (FStar_Syntax_Util.unfold_lazy i)
in (infer env uu____7301))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) -> begin
(

let subst_rc_opt = (fun subst1 rc_opt1 -> (match (rc_opt1) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = uu____7352; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = uu____7353}) -> begin
rc_opt1
end
| FStar_Pervasives_Native.None -> begin
rc_opt1
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____7359 = (

let uu___775_7360 = rc
in (

let uu____7361 = (

let uu____7366 = (

let uu____7369 = (FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ)
in (FStar_Syntax_Subst.subst subst1 uu____7369))
in FStar_Pervasives_Native.Some (uu____7366))
in {FStar_Syntax_Syntax.residual_effect = uu___775_7360.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____7361; FStar_Syntax_Syntax.residual_flags = uu___775_7360.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____7359))
end))
in (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let subst1 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let body1 = (FStar_Syntax_Subst.subst subst1 body)
in (

let rc_opt1 = (subst_rc_opt subst1 rc_opt)
in (

let env1 = (

let uu___781_7381 = env
in (

let uu____7382 = (FStar_TypeChecker_Env.push_binders env.tcenv binders1)
in {tcenv = uu____7382; subst = uu___781_7381.subst; tc_const = uu___781_7381.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____7408 -> (match (uu____7408) with
| (bv, qual) -> begin
(

let sort = (star_type' env1 bv.FStar_Syntax_Syntax.sort)
in (((

let uu___788_7431 = bv
in {FStar_Syntax_Syntax.ppname = uu___788_7431.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___788_7431.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders1)
in (

let uu____7432 = (FStar_List.fold_left (fun uu____7463 uu____7464 -> (match (((uu____7463), (uu____7464))) with
| ((env2, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____7522 = (is_C c)
in (match (uu____7522) with
| true -> begin
(

let xw = (

let uu____7532 = (star_type' env2 c)
in (FStar_Syntax_Syntax.gen_bv (Prims.op_Hat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w") FStar_Pervasives_Native.None uu____7532))
in (

let x = (

let uu___800_7535 = bv
in (

let uu____7536 = (

let uu____7539 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env2 c uu____7539))
in {FStar_Syntax_Syntax.ppname = uu___800_7535.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___800_7535.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7536}))
in (

let env3 = (

let uu___803_7541 = env2
in (

let uu____7542 = (

let uu____7545 = (

let uu____7546 = (

let uu____7553 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (uu____7553)))
in FStar_Syntax_Syntax.NT (uu____7546))
in (uu____7545)::env2.subst)
in {tcenv = uu___803_7541.tcenv; subst = uu____7542; tc_const = uu___803_7541.tc_const}))
in (

let uu____7558 = (

let uu____7561 = (FStar_Syntax_Syntax.mk_binder x)
in (

let uu____7562 = (

let uu____7565 = (FStar_Syntax_Syntax.mk_binder xw)
in (uu____7565)::acc)
in (uu____7561)::uu____7562))
in ((env3), (uu____7558))))))
end
| uu____7568 -> begin
(

let x = (

let uu___806_7571 = bv
in (

let uu____7572 = (star_type' env2 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___806_7571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___806_7571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7572}))
in (

let uu____7575 = (

let uu____7578 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7578)::acc)
in ((env2), (uu____7575))))
end)))
end)) ((env1), ([])) binders1)
in (match (uu____7432) with
| (env2, u_binders) -> begin
(

let u_binders1 = (FStar_List.rev u_binders)
in (

let uu____7598 = (

let check_what = (

let uu____7624 = (is_monadic rc_opt1)
in (match (uu____7624) with
| true -> begin
check_m
end
| uu____7639 -> begin
check_n
end))
in (

let uu____7641 = (check_what env2 body1)
in (match (uu____7641) with
| (t, s_body, u_body) -> begin
(

let uu____7661 = (

let uu____7664 = (

let uu____7665 = (is_monadic rc_opt1)
in (match (uu____7665) with
| true -> begin
M (t)
end
| uu____7668 -> begin
N (t)
end))
in (comp_of_nm uu____7664))
in ((uu____7661), (s_body), (u_body)))
end)))
in (match (uu____7598) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders1 comp)
in (

let s_rc_opt = (match (rc_opt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let rc1 = (

let uu____7705 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___6_7711 -> (match (uu___6_7711) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____7714 -> begin
false
end))))
in (match (uu____7705) with
| true -> begin
(

let uu____7717 = (FStar_List.filter (fun uu___7_7721 -> (match (uu___7_7721) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____7724 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None uu____7717))
end
| uu____7728 -> begin
rc
end))
in FStar_Pervasives_Native.Some (rc1))
end
| FStar_Pervasives_Native.Some (rt) -> begin
(

let uu____7735 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___8_7741 -> (match (uu___8_7741) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____7744 -> begin
false
end))))
in (match (uu____7735) with
| true -> begin
(

let flags = (FStar_List.filter (fun uu___9_7753 -> (match (uu___9_7753) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____7756 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____7758 = (

let uu____7759 = (

let uu____7764 = (double_star rt)
in FStar_Pervasives_Native.Some (uu____7764))
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid uu____7759 flags))
in FStar_Pervasives_Native.Some (uu____7758)))
end
| uu____7769 -> begin
(

let uu____7771 = (

let uu___847_7772 = rc
in (

let uu____7773 = (

let uu____7778 = (star_type' env2 rt)
in FStar_Pervasives_Native.Some (uu____7778))
in {FStar_Syntax_Syntax.residual_effect = uu___847_7772.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____7773; FStar_Syntax_Syntax.residual_flags = uu___847_7772.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____7771))
end))
end)
end)
in (

let uu____7783 = (

let comp1 = (

let uu____7791 = (is_monadic rc_opt1)
in (

let uu____7793 = (FStar_Syntax_Subst.subst env2.subst s_body)
in (trans_G env2 (FStar_Syntax_Util.comp_result comp) uu____7791 uu____7793)))
in (

let uu____7794 = (FStar_Syntax_Util.ascribe u_body ((FStar_Util.Inr (comp1)), (FStar_Pervasives_Native.None)))
in ((uu____7794), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp1))))))
in (match (uu____7783) with
| (u_body1, u_rc_opt) -> begin
(

let s_body1 = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders1 = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (

let uu____7832 = (

let uu____7833 = (

let uu____7852 = (

let uu____7855 = (FStar_Syntax_Subst.closing_of_binders s_binders1)
in (subst_rc_opt uu____7855 s_rc_opt))
in ((s_binders1), (s_body1), (uu____7852)))
in FStar_Syntax_Syntax.Tm_abs (uu____7833))
in (mk1 uu____7832))
in (

let u_body2 = (FStar_Syntax_Subst.close u_binders1 u_body1)
in (

let u_binders2 = (FStar_Syntax_Subst.close_binders u_binders1)
in (

let u_term = (

let uu____7875 = (

let uu____7876 = (

let uu____7895 = (

let uu____7898 = (FStar_Syntax_Subst.closing_of_binders u_binders2)
in (subst_rc_opt uu____7898 u_rc_opt))
in ((u_binders2), (u_body2), (uu____7895)))
in FStar_Syntax_Syntax.Tm_abs (uu____7876))
in (mk1 uu____7875))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.p = uu____7914}; FStar_Syntax_Syntax.fv_delta = uu____7915; FStar_Syntax_Syntax.fv_qual = uu____7916}) -> begin
(

let uu____7919 = (

let uu____7924 = (FStar_TypeChecker_Env.lookup_lid env.tcenv lid)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7924))
in (match (uu____7919) with
| (uu____7955, t) -> begin
(

let uu____7957 = (

let uu____7958 = (normalize1 t)
in N (uu____7958))
in ((uu____7957), (e), (e)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____7959; FStar_Syntax_Syntax.vars = uu____7960}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____8039 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8039) with
| (unary_op1, uu____8063) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8134; FStar_Syntax_Syntax.vars = uu____8135}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____8231 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8231) with
| (unary_op1, uu____8255) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____8334; FStar_Syntax_Syntax.vars = uu____8335}, ((a, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____8373 = (infer env a)
in (match (uu____8373) with
| (t, s, u) -> begin
(

let uu____8389 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8389) with
| (head1, uu____8413) -> begin
(

let uu____8438 = (

let uu____8439 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in N (uu____8439))
in (

let uu____8440 = (

let uu____8441 = (

let uu____8442 = (

let uu____8459 = (

let uu____8470 = (FStar_Syntax_Syntax.as_arg s)
in (uu____8470)::[])
in ((head1), (uu____8459)))
in FStar_Syntax_Syntax.Tm_app (uu____8442))
in (mk1 uu____8441))
in (

let uu____8507 = (

let uu____8508 = (

let uu____8509 = (

let uu____8526 = (

let uu____8537 = (FStar_Syntax_Syntax.as_arg u)
in (uu____8537)::[])
in ((head1), (uu____8526)))
in FStar_Syntax_Syntax.Tm_app (uu____8509))
in (mk1 uu____8508))
in ((uu____8438), (uu____8440), (uu____8507)))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8574; FStar_Syntax_Syntax.vars = uu____8575}, ((a1, uu____8577))::(a2)::[]) -> begin
(

let uu____8633 = (infer env a1)
in (match (uu____8633) with
| (t, s, u) -> begin
(

let uu____8649 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8649) with
| (head1, uu____8673) -> begin
(

let uu____8698 = (

let uu____8699 = (

let uu____8700 = (

let uu____8717 = (

let uu____8728 = (FStar_Syntax_Syntax.as_arg s)
in (uu____8728)::(a2)::[])
in ((head1), (uu____8717)))
in FStar_Syntax_Syntax.Tm_app (uu____8700))
in (mk1 uu____8699))
in (

let uu____8773 = (

let uu____8774 = (

let uu____8775 = (

let uu____8792 = (

let uu____8803 = (FStar_Syntax_Syntax.as_arg u)
in (uu____8803)::(a2)::[])
in ((head1), (uu____8792)))
in FStar_Syntax_Syntax.Tm_app (uu____8775))
in (mk1 uu____8774))
in ((t), (uu____8698), (uu____8773))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____8848; FStar_Syntax_Syntax.vars = uu____8849}, uu____8850) -> begin
(

let uu____8875 = (

let uu____8881 = (

let uu____8883 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8883))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____8881)))
in (FStar_Errors.raise_error uu____8875 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8893; FStar_Syntax_Syntax.vars = uu____8894}, uu____8895) -> begin
(

let uu____8920 = (

let uu____8926 = (

let uu____8928 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8928))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____8926)))
in (FStar_Errors.raise_error uu____8920 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____8964 = (check_n env head1)
in (match (uu____8964) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____8987 = (

let uu____8988 = (FStar_Syntax_Subst.compress t)
in uu____8988.FStar_Syntax_Syntax.n)
in (match (uu____8987) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8992) -> begin
true
end
| uu____9008 -> begin
false
end)))
in (

let rec flatten1 = (fun t -> (

let uu____9030 = (

let uu____9031 = (FStar_Syntax_Subst.compress t)
in uu____9031.FStar_Syntax_Syntax.n)
in (match (uu____9030) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t1, uu____9050); FStar_Syntax_Syntax.pos = uu____9051; FStar_Syntax_Syntax.vars = uu____9052}) when (is_arrow t1) -> begin
(

let uu____9081 = (flatten1 t1)
in (match (uu____9081) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____9181, uu____9182) -> begin
(flatten1 e1)
end
| uu____9223 -> begin
(

let uu____9224 = (

let uu____9230 = (

let uu____9232 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" uu____9232))
in ((FStar_Errors.Fatal_NotFunctionType), (uu____9230)))
in (FStar_Errors.raise_err uu____9224))
end)))
in (

let uu____9250 = (flatten1 t_head)
in (match (uu____9250) with
| (binders, comp) -> begin
(

let n1 = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(

let uu____9325 = (

let uu____9331 = (

let uu____9333 = (FStar_Util.string_of_int n1)
in (

let uu____9335 = (FStar_Util.string_of_int (n' - n1))
in (

let uu____9337 = (FStar_Util.string_of_int n1)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." uu____9333 uu____9335 uu____9337))))
in ((FStar_Errors.Fatal_BinderAndArgsLengthMismatch), (uu____9331)))
in (FStar_Errors.raise_err uu____9325))
end
| uu____9341 -> begin
()
end);
(

let uu____9343 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____9343) with
| (binders1, comp1) -> begin
(

let rec final_type = (fun subst1 uu____9396 args1 -> (match (uu____9396) with
| (binders2, comp2) -> begin
(match (((binders2), (args1))) with
| ([], []) -> begin
(

let uu____9496 = (FStar_Syntax_Subst.subst_comp subst1 comp2)
in (nm_of_comp uu____9496))
end
| (binders3, []) -> begin
(

let uu____9534 = (

let uu____9535 = (

let uu____9538 = (

let uu____9539 = (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders3), (comp2)))))
in (FStar_Syntax_Subst.subst subst1 uu____9539))
in (FStar_Syntax_Subst.compress uu____9538))
in uu____9535.FStar_Syntax_Syntax.n)
in (match (uu____9534) with
| FStar_Syntax_Syntax.Tm_arrow (binders4, comp3) -> begin
(

let uu____9572 = (

let uu____9573 = (

let uu____9574 = (

let uu____9589 = (FStar_Syntax_Subst.close_comp binders4 comp3)
in ((binders4), (uu____9589)))
in FStar_Syntax_Syntax.Tm_arrow (uu____9574))
in (mk1 uu____9573))
in N (uu____9572))
end
| uu____9602 -> begin
(failwith "wat?")
end))
end
| ([], (uu____9604)::uu____9605) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____9658))::binders3, ((arg, uu____9661))::args2) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst1) ((binders3), (comp2)) args2)
end)
end))
in (

let final_type1 = (final_type [] ((binders1), (comp1)) args)
in (

let uu____9748 = (FStar_List.splitAt n' binders1)
in (match (uu____9748) with
| (binders2, uu____9782) -> begin
(

let uu____9815 = (

let uu____9838 = (FStar_List.map2 (fun uu____9900 uu____9901 -> (match (((uu____9900), (uu____9901))) with
| ((bv, uu____9949), (arg, q)) -> begin
(

let uu____9978 = (

let uu____9979 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in uu____9979.FStar_Syntax_Syntax.n)
in (match (uu____9978) with
| FStar_Syntax_Syntax.Tm_type (uu____10000) -> begin
(

let uu____10001 = (

let uu____10008 = (star_type' env arg)
in ((uu____10008), (q)))
in ((uu____10001), ((((arg), (q)))::[])))
end
| uu____10045 -> begin
(

let uu____10046 = (check_n env arg)
in (match (uu____10046) with
| (uu____10071, s_arg, u_arg) -> begin
(

let uu____10074 = (

let uu____10083 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____10083) with
| true -> begin
(

let uu____10094 = (

let uu____10101 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((uu____10101), (q)))
in (uu____10094)::(((u_arg), (q)))::[])
end
| uu____10124 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (uu____10074)))
end))
end))
end)) binders2 args)
in (FStar_List.split uu____9838))
in (match (uu____9815) with
| (s_args, u_args) -> begin
(

let u_args1 = (FStar_List.flatten u_args)
in (

let uu____10229 = (mk1 (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (

let uu____10242 = (mk1 (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args1)))))
in ((final_type1), (uu____10229), (uu____10242)))))
end))
end))))
end));
)))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 infer check_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches infer)
end
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____10311) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____10317) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____10323, uu____10324) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____10366 = (

let uu____10367 = (env.tc_const c)
in N (uu____10367))
in ((uu____10366), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qt) -> begin
((N (FStar_Syntax_Syntax.t_term)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_let (uu____10374) -> begin
(

let uu____10388 = (

let uu____10390 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" uu____10390))
in (failwith uu____10388))
end
| FStar_Syntax_Syntax.Tm_type (uu____10399) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10407) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____10429) -> begin
(

let uu____10436 = (

let uu____10438 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" uu____10438))
in (failwith uu____10436))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10447) -> begin
(

let uu____10460 = (

let uu____10462 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10462))
in (failwith uu____10460))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____10471) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____10501 = (

let uu____10503 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10503))
in (failwith uu____10501))
end)))))
and mk_match : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e0.FStar_Syntax_Syntax.pos))
in (

let uu____10552 = (check_n env e0)
in (match (uu____10552) with
| (uu____10565, s_e0, u_e0) -> begin
(

let uu____10568 = (

let uu____10597 = (FStar_List.map (fun b -> (

let uu____10658 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____10658) with
| (pat, FStar_Pervasives_Native.None, body) -> begin
(

let env1 = (

let uu___1122_10700 = env
in (

let uu____10701 = (

let uu____10702 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.tcenv uu____10702))
in {tcenv = uu____10701; subst = uu___1122_10700.subst; tc_const = uu___1122_10700.tc_const}))
in (

let uu____10705 = (f env1 body)
in (match (uu____10705) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (FStar_Pervasives_Native.None), (((s_body), (u_body), (body))))))
end)))
end
| uu____10777 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_WhenClauseNotSupported), ("No when clauses in the definition language")))
end))) branches)
in (FStar_List.split uu____10597))
in (match (uu____10568) with
| (nms, branches1) -> begin
(

let t1 = (

let uu____10883 = (FStar_List.hd nms)
in (match (uu____10883) with
| M (t1) -> begin
t1
end
| N (t1) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___10_10892 -> (match (uu___10_10892) with
| M (uu____10894) -> begin
true
end
| uu____10896 -> begin
false
end)) nms)
in (

let uu____10898 = (

let uu____10935 = (FStar_List.map2 (fun nm uu____11025 -> (match (uu____11025) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| (N (t2), false) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (M (t2), true) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let uu____11209 = (check env original_body (M (t2)))
in (match (uu____11209) with
| (uu____11246, s_body1, u_body1) -> begin
((M (t2)), (((pat), (guard), (s_body1))), (((pat), (guard), (u_body1))))
end))
end
| (M (uu____11285), false) -> begin
(failwith "impossible")
end)
end)) nms branches1)
in (FStar_List.unzip3 uu____10935))
in (match (uu____10898) with
| (nms1, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk1 env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_branches1 = (FStar_List.map (fun uu____11474 -> (match (uu____11474) with
| (pat, guard, s_body) -> begin
(

let s_body1 = (

let uu____11525 = (

let uu____11526 = (

let uu____11543 = (

let uu____11554 = (

let uu____11563 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____11566 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____11563), (uu____11566))))
in (uu____11554)::[])
in ((s_body), (uu____11543)))
in FStar_Syntax_Syntax.Tm_app (uu____11526))
in (mk1 uu____11525))
in ((pat), (guard), (s_body1)))
end)) s_branches)
in (

let s_branches2 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches1)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (

let uu____11701 = (

let uu____11702 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____11702)::[])
in (

let uu____11721 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches2)))))
in (FStar_Syntax_Util.abs uu____11701 uu____11721 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))
in (

let t1_star = (

let uu____11745 = (

let uu____11754 = (

let uu____11761 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____11761))
in (uu____11754)::[])
in (

let uu____11780 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____11745 uu____11780)))
in (

let uu____11783 = (mk1 (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))))
in (

let uu____11822 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((M (t1)), (uu____11783), (uu____11822)))))))))))
end
| uu____11841 -> begin
(

let s_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (

let uu____11932 = (

let uu____11933 = (

let uu____11934 = (

let uu____11961 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches1)))))
in ((uu____11961), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____11934))
in (mk1 uu____11933))
in (

let uu____12020 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((N (t1)), (uu____11932), (uu____12020)))))))
end)
end))))
end))
end))))
and mk_let : env_  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.term  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env binding e2 proceed ensure_m -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos))
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (

let uu____12085 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____12085)::[])
in (

let uu____12104 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____12104) with
| (x_binders1, e21) -> begin
(

let uu____12117 = (infer env e1)
in (match (uu____12117) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____12134 = (is_C t1)
in (match (uu____12134) with
| true -> begin
(

let uu___1208_12137 = binding
in (

let uu____12138 = (

let uu____12141 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 uu____12141))
in {FStar_Syntax_Syntax.lbname = uu___1208_12137.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1208_12137.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____12138; FStar_Syntax_Syntax.lbeff = uu___1208_12137.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___1208_12137.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1208_12137.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1208_12137.FStar_Syntax_Syntax.lbpos}))
end
| uu____12142 -> begin
binding
end))
in (

let env1 = (

let uu___1211_12145 = env
in (

let uu____12146 = (FStar_TypeChecker_Env.push_bv env.tcenv (

let uu___1213_12148 = x
in {FStar_Syntax_Syntax.ppname = uu___1213_12148.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1213_12148.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {tcenv = uu____12146; subst = uu___1211_12145.subst; tc_const = uu___1211_12145.tc_const}))
in (

let uu____12149 = (proceed env1 e21)
in (match (uu____12149) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___1220_12166 = binding
in (

let uu____12167 = (star_type' env1 binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___1220_12166.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1220_12166.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____12167; FStar_Syntax_Syntax.lbeff = uu___1220_12166.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___1220_12166.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1220_12166.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1220_12166.FStar_Syntax_Syntax.lbpos}))
in (

let uu____12170 = (

let uu____12171 = (

let uu____12172 = (

let uu____12186 = (FStar_Syntax_Subst.close x_binders1 s_e2)
in ((((false), (((

let uu___1223_12203 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___1223_12203.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1223_12203.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1223_12203.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1223_12203.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1; FStar_Syntax_Syntax.lbattrs = uu___1223_12203.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1223_12203.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____12186)))
in FStar_Syntax_Syntax.Tm_let (uu____12172))
in (mk1 uu____12171))
in (

let uu____12204 = (

let uu____12205 = (

let uu____12206 = (

let uu____12220 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___1225_12237 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___1225_12237.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1225_12237.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1225_12237.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1225_12237.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___1225_12237.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1225_12237.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____12220)))
in FStar_Syntax_Syntax.Tm_let (uu____12206))
in (mk1 uu____12205))
in ((nm_rec), (uu____12170), (uu____12204)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___1232_12242 = binding
in {FStar_Syntax_Syntax.lbname = uu___1232_12242.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1232_12242.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___1232_12242.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1232_12242.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1232_12242.FStar_Syntax_Syntax.lbpos})
in (

let env1 = (

let uu___1235_12244 = env
in (

let uu____12245 = (FStar_TypeChecker_Env.push_bv env.tcenv (

let uu___1237_12247 = x
in {FStar_Syntax_Syntax.ppname = uu___1237_12247.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1237_12247.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {tcenv = uu____12245; subst = uu___1235_12244.subst; tc_const = uu___1235_12244.tc_const}))
in (

let uu____12248 = (ensure_m env1 e21)
in (match (uu____12248) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk1 env1 t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_e21 = (

let uu____12272 = (

let uu____12273 = (

let uu____12290 = (

let uu____12301 = (

let uu____12310 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____12313 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____12310), (uu____12313))))
in (uu____12301)::[])
in ((s_e2), (uu____12290)))
in FStar_Syntax_Syntax.Tm_app (uu____12273))
in (mk1 uu____12272))
in (

let s_e22 = (FStar_Syntax_Util.abs x_binders1 s_e21 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let body = (

let uu____12355 = (

let uu____12356 = (

let uu____12373 = (

let uu____12384 = (

let uu____12393 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e22), (uu____12393)))
in (uu____12384)::[])
in ((s_e1), (uu____12373)))
in FStar_Syntax_Syntax.Tm_app (uu____12356))
in (mk1 uu____12355))
in (

let uu____12429 = (

let uu____12430 = (

let uu____12431 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____12431)::[])
in (FStar_Syntax_Util.abs uu____12430 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
in (

let uu____12450 = (

let uu____12451 = (

let uu____12452 = (

let uu____12466 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___1249_12483 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___1249_12483.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1249_12483.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1249_12483.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1249_12483.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___1249_12483.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1249_12483.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____12466)))
in FStar_Syntax_Syntax.Tm_let (uu____12452))
in (mk1 uu____12451))
in ((M (t2)), (uu____12429), (uu____12450)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____12493 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in N (uu____12493))
in (

let uu____12494 = (check env e mn)
in (match (uu____12494) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____12510 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____12533 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in M (uu____12533))
in (

let uu____12534 = (check env e mn)
in (match (uu____12534) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____12550 -> begin
(failwith "[check_m]: impossible")
end))))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> ((

let uu____12583 = (

let uu____12585 = (is_C c)
in (not (uu____12585)))
in (match (uu____12583) with
| true -> begin
(failwith "not a C")
end
| uu____12589 -> begin
()
end));
(

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (

let uu____12599 = (

let uu____12600 = (FStar_Syntax_Subst.compress c)
in uu____12600.FStar_Syntax_Syntax.n)
in (match (uu____12599) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____12629 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____12629) with
| (wp_head, wp_args) -> begin
((

let uu____12673 = ((not ((Prims.op_Equality (FStar_List.length wp_args) (FStar_List.length args)))) || (

let uu____12692 = (

let uu____12694 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head uu____12694))
in (not (uu____12692))))
in (match (uu____12673) with
| true -> begin
(failwith "mismatch")
end
| uu____12705 -> begin
()
end));
(

let uu____12707 = (

let uu____12708 = (

let uu____12725 = (FStar_List.map2 (fun uu____12763 uu____12764 -> (match (((uu____12763), (uu____12764))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q1 -> (

let uu____12826 = (FStar_Syntax_Syntax.is_implicit q1)
in (match (uu____12826) with
| true -> begin
"implicit"
end
| uu____12831 -> begin
"explicit"
end)))
in ((

let uu____12835 = (

let uu____12837 = (FStar_Syntax_Util.eq_aqual q q')
in (Prims.op_disEquality uu____12837 FStar_Syntax_Util.Equal))
in (match (uu____12835) with
| true -> begin
(

let uu____12839 = (

let uu____12845 = (

let uu____12847 = (print_implicit q)
in (

let uu____12849 = (print_implicit q')
in (FStar_Util.format2 "Incoherent implicit qualifiers %s %s\n" uu____12847 uu____12849)))
in ((FStar_Errors.Warning_IncoherentImplicitQualifier), (uu____12845)))
in (FStar_Errors.log_issue head1.FStar_Syntax_Syntax.pos uu____12839))
end
| uu____12853 -> begin
()
end));
(

let uu____12855 = (trans_F_ env arg wp_arg)
in ((uu____12855), (q)));
))
end)) args wp_args)
in ((head1), (uu____12725)))
in FStar_Syntax_Syntax.Tm_app (uu____12708))
in (mk1 uu____12707));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders1 = (FStar_Syntax_Util.name_binders binders)
in (

let uu____12901 = (FStar_Syntax_Subst.open_comp binders1 comp)
in (match (uu____12901) with
| (binders_orig, comp1) -> begin
(

let uu____12908 = (

let uu____12925 = (FStar_List.map (fun uu____12965 -> (match (uu____12965) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____12993 = (is_C h)
in (match (uu____12993) with
| true -> begin
(

let w' = (

let uu____13009 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.op_Hat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w\'") FStar_Pervasives_Native.None uu____13009))
in (

let uu____13011 = (

let uu____13020 = (

let uu____13029 = (

let uu____13036 = (

let uu____13037 = (

let uu____13038 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h uu____13038))
in (FStar_Syntax_Syntax.null_bv uu____13037))
in ((uu____13036), (q)))
in (uu____13029)::[])
in (((w'), (q)))::uu____13020)
in ((w'), (uu____13011))))
end
| uu____13069 -> begin
(

let x = (

let uu____13072 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.op_Hat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__x") FStar_Pervasives_Native.None uu____13072))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig)
in (FStar_List.split uu____12925))
in (match (uu____12908) with
| (bvs, binders2) -> begin
(

let binders3 = (FStar_List.flatten binders2)
in (

let comp2 = (

let uu____13146 = (

let uu____13149 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig uu____13149))
in (FStar_Syntax_Subst.subst_comp uu____13146 comp1))
in (

let app = (

let uu____13153 = (

let uu____13154 = (

let uu____13171 = (FStar_List.map (fun bv -> (

let uu____13190 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____13191 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____13190), (uu____13191))))) bvs)
in ((wp), (uu____13171)))
in FStar_Syntax_Syntax.Tm_app (uu____13154))
in (mk1 uu____13153))
in (

let comp3 = (

let uu____13206 = (type_of_comp comp2)
in (

let uu____13207 = (is_monadic_comp comp2)
in (trans_G env uu____13206 uu____13207 app)))
in (FStar_Syntax_Util.arrow binders3 comp3)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____13210, uu____13211) -> begin
(trans_F_ env e wp)
end
| uu____13252 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic1 wp -> (match (is_monadic1) with
| true -> begin
(

let uu____13260 = (

let uu____13261 = (star_type' env h)
in (

let uu____13264 = (

let uu____13275 = (

let uu____13284 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (uu____13284)))
in (uu____13275)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu____13261; FStar_Syntax_Syntax.effect_args = uu____13264; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____13260))
end
| uu____13308 -> begin
(

let uu____13310 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total uu____13310))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____13331 = (n env.tcenv t)
in (star_type' env uu____13331)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (

let uu____13351 = (n env.tcenv t)
in (check_n env uu____13351)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let uu____13368 = (n env.tcenv c)
in (

let uu____13369 = (n env.tcenv wp)
in (trans_F_ env uu____13368 uu____13369))))




