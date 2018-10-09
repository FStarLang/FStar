
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

let uu___362_123 = a
in (

let uu____124 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___362_123.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___362_123.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____124}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in ((

let uu____134 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____134) with
| true -> begin
((d "Elaborating extra WP combinators");
(

let uu____136 = (FStar_Syntax_Print.term_to_string wp_a1)
in (FStar_Util.print1 "wp_a is: %s\n" uu____136));
)
end
| uu____137 -> begin
()
end));
(

let rec collect_binders = (fun t -> (

let uu____152 = (

let uu____153 = (

let uu____156 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____156))
in uu____153.FStar_Syntax_Syntax.n)
in (match (uu____152) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uu____191) -> begin
t1
end
| uu____200 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (

let uu____201 = (collect_binders rest)
in (FStar_List.append bs uu____201)))
end
| FStar_Syntax_Syntax.Tm_type (uu____216) -> begin
[]
end
| uu____223 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let gamma = (

let uu____247 = (collect_binders wp_a1)
in (FStar_All.pipe_right uu____247 FStar_Syntax_Util.name_binders))
in ((

let uu____273 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____273) with
| true -> begin
(

let uu____274 = (

let uu____275 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" uu____275))
in (d uu____274))
end
| uu____276 -> begin
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

let uu____309 = (FStar_TypeChecker_Util.mk_toplevel_definition env1 lident def)
in (match (uu____309) with
| (sigelt, fv) -> begin
((

let uu____317 = (

let uu____320 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____320)
in (FStar_ST.op_Colon_Equals sigelts uu____317));
fv;
)
end)))
in (

let binders_of_list1 = (FStar_List.map (fun uu____442 -> (match (uu____442) with
| (t, b) -> begin
(

let uu____453 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (uu____453)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (

let uu____492 = (FStar_Syntax_Syntax.as_implicit true)
in (((FStar_Pervasives_Native.fst t)), (uu____492)))))
in (

let args_of_binders1 = (FStar_List.map (fun bv -> (

let uu____525 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst bv))
in (FStar_Syntax_Syntax.as_arg uu____525))))
in (

let uu____528 = (

let uu____545 = (

let mk2 = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let body = (

let uu____569 = (

let uu____572 = (FStar_Syntax_Syntax.bv_to_name t)
in (f uu____572))
in (FStar_Syntax_Util.arrow gamma uu____569))
in (

let uu____573 = (

let uu____574 = (

let uu____583 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____590 = (

let uu____599 = (FStar_Syntax_Syntax.mk_binder t)
in (uu____599)::[])
in (uu____583)::uu____590))
in (FStar_List.append binders uu____574))
in (FStar_Syntax_Util.abs uu____573 body FStar_Pervasives_Native.None)))))
in (

let uu____630 = (mk2 FStar_Syntax_Syntax.mk_Total)
in (

let uu____631 = (mk2 FStar_Syntax_Syntax.mk_GTotal)
in ((uu____630), (uu____631)))))
in (match (uu____545) with
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

let uu____671 = (

let uu____672 = (

let uu____689 = (

let uu____700 = (FStar_List.map (fun uu____722 -> (match (uu____722) with
| (bv, uu____734) -> begin
(

let uu____739 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____740 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____739), (uu____740))))
end)) binders)
in (

let uu____741 = (

let uu____748 = (

let uu____753 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____754 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____753), (uu____754))))
in (

let uu____755 = (

let uu____762 = (

let uu____767 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (uu____767)))
in (uu____762)::[])
in (uu____748)::uu____755))
in (FStar_List.append uu____700 uu____741)))
in ((fv), (uu____689)))
in FStar_Syntax_Syntax.Tm_app (uu____672))
in (mk1 uu____671)))
in ((env), ((mk_app1 ctx_fv)), ((mk_app1 gctx_fv))))))))
end))
in (match (uu____528) with
| (env1, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let x = (

let uu____838 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None uu____838))
in (

let ret1 = (

let uu____842 = (

let uu____843 = (

let uu____846 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx uu____846))
in (FStar_Syntax_Util.residual_tot uu____843))
in FStar_Pervasives_Native.Some (uu____842))
in (

let body = (

let uu____850 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma uu____850 ret1))
in (

let uu____853 = (

let uu____854 = (mk_all_implicit binders)
in (

let uu____861 = (binders_of_list1 ((((a1), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append uu____854 uu____861)))
in (FStar_Syntax_Util.abs uu____853 body ret1))))))
in (

let c_pure1 = (

let uu____889 = (mk_lid "pure")
in (register env1 uu____889 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let l = (

let uu____896 = (

let uu____897 = (

let uu____898 = (

let uu____907 = (

let uu____914 = (

let uu____915 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____915))
in (FStar_Syntax_Syntax.mk_binder uu____914))
in (uu____907)::[])
in (

let uu____928 = (

let uu____931 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____931))
in (FStar_Syntax_Util.arrow uu____898 uu____928)))
in (mk_gctx uu____897))
in (FStar_Syntax_Syntax.gen_bv "l" FStar_Pervasives_Native.None uu____896))
in (

let r = (

let uu____933 = (

let uu____934 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____934))
in (FStar_Syntax_Syntax.gen_bv "r" FStar_Pervasives_Native.None uu____933))
in (

let ret1 = (

let uu____938 = (

let uu____939 = (

let uu____942 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____942))
in (FStar_Syntax_Util.residual_tot uu____939))
in FStar_Pervasives_Native.Some (uu____938))
in (

let outer_body = (

let gamma_as_args = (args_of_binders1 gamma)
in (

let inner_body = (

let uu____952 = (FStar_Syntax_Syntax.bv_to_name l)
in (

let uu____955 = (

let uu____966 = (

let uu____969 = (

let uu____970 = (

let uu____971 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app uu____971 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg uu____970))
in (uu____969)::[])
in (FStar_List.append gamma_as_args uu____966))
in (FStar_Syntax_Util.mk_app uu____952 uu____955)))
in (FStar_Syntax_Util.abs gamma inner_body ret1)))
in (

let uu____974 = (

let uu____975 = (mk_all_implicit binders)
in (

let uu____982 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append uu____975 uu____982)))
in (FStar_Syntax_Util.abs uu____974 outer_body ret1))))))))
in (

let c_app1 = (

let uu____1018 = (mk_lid "app")
in (register env1 uu____1018 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1027 = (

let uu____1036 = (

let uu____1043 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1043))
in (uu____1036)::[])
in (

let uu____1056 = (

let uu____1059 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____1059))
in (FStar_Syntax_Util.arrow uu____1027 uu____1056)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____1062 = (

let uu____1063 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____1063))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____1062))
in (

let ret1 = (

let uu____1067 = (

let uu____1068 = (

let uu____1071 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1071))
in (FStar_Syntax_Util.residual_tot uu____1068))
in FStar_Pervasives_Native.Some (uu____1067))
in (

let uu____1072 = (

let uu____1073 = (mk_all_implicit binders)
in (

let uu____1080 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a11), (false)))::[]))
in (FStar_List.append uu____1073 uu____1080)))
in (

let uu____1115 = (

let uu____1118 = (

let uu____1129 = (

let uu____1132 = (

let uu____1133 = (

let uu____1144 = (

let uu____1147 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1147)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1144))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1133))
in (

let uu____1156 = (

let uu____1159 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1159)::[])
in (uu____1132)::uu____1156))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1129))
in (FStar_Syntax_Util.mk_app c_app1 uu____1118))
in (FStar_Syntax_Util.abs uu____1072 uu____1115 ret1)))))))))
in (

let c_lift11 = (

let uu____1169 = (mk_lid "lift1")
in (register env1 uu____1169 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1179 = (

let uu____1188 = (

let uu____1195 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1195))
in (

let uu____1196 = (

let uu____1205 = (

let uu____1212 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder uu____1212))
in (uu____1205)::[])
in (uu____1188)::uu____1196))
in (

let uu____1231 = (

let uu____1234 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal uu____1234))
in (FStar_Syntax_Util.arrow uu____1179 uu____1231)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____1237 = (

let uu____1238 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____1238))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____1237))
in (

let a2 = (

let uu____1240 = (

let uu____1241 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1241))
in (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None uu____1240))
in (

let ret1 = (

let uu____1245 = (

let uu____1246 = (

let uu____1249 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx uu____1249))
in (FStar_Syntax_Util.residual_tot uu____1246))
in FStar_Pervasives_Native.Some (uu____1245))
in (

let uu____1250 = (

let uu____1251 = (mk_all_implicit binders)
in (

let uu____1258 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a11), (false)))::(((a2), (false)))::[]))
in (FStar_List.append uu____1251 uu____1258)))
in (

let uu____1301 = (

let uu____1304 = (

let uu____1315 = (

let uu____1318 = (

let uu____1319 = (

let uu____1330 = (

let uu____1333 = (

let uu____1334 = (

let uu____1345 = (

let uu____1348 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1348)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1345))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1334))
in (

let uu____1357 = (

let uu____1360 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1360)::[])
in (uu____1333)::uu____1357))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1330))
in (FStar_Syntax_Util.mk_app c_app1 uu____1319))
in (

let uu____1369 = (

let uu____1372 = (FStar_Syntax_Syntax.bv_to_name a2)
in (uu____1372)::[])
in (uu____1318)::uu____1369))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1315))
in (FStar_Syntax_Util.mk_app c_app1 uu____1304))
in (FStar_Syntax_Util.abs uu____1250 uu____1301 ret1)))))))))))
in (

let c_lift21 = (

let uu____1382 = (mk_lid "lift2")
in (register env1 uu____1382 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1391 = (

let uu____1400 = (

let uu____1407 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1407))
in (uu____1400)::[])
in (

let uu____1420 = (

let uu____1423 = (

let uu____1424 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1424))
in (FStar_Syntax_Syntax.mk_Total uu____1423))
in (FStar_Syntax_Util.arrow uu____1391 uu____1420)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let ret1 = (

let uu____1429 = (

let uu____1430 = (

let uu____1433 = (

let uu____1434 = (

let uu____1443 = (

let uu____1450 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1450))
in (uu____1443)::[])
in (

let uu____1463 = (

let uu____1466 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____1466))
in (FStar_Syntax_Util.arrow uu____1434 uu____1463)))
in (mk_ctx uu____1433))
in (FStar_Syntax_Util.residual_tot uu____1430))
in FStar_Pervasives_Native.Some (uu____1429))
in (

let e1 = (

let uu____1468 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" FStar_Pervasives_Native.None uu____1468))
in (

let body = (

let uu____1472 = (

let uu____1473 = (

let uu____1482 = (FStar_Syntax_Syntax.mk_binder e1)
in (uu____1482)::[])
in (FStar_List.append gamma uu____1473))
in (

let uu____1507 = (

let uu____1510 = (FStar_Syntax_Syntax.bv_to_name f)
in (

let uu____1513 = (

let uu____1524 = (

let uu____1525 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg uu____1525))
in (

let uu____1526 = (args_of_binders1 gamma)
in (uu____1524)::uu____1526))
in (FStar_Syntax_Util.mk_app uu____1510 uu____1513)))
in (FStar_Syntax_Util.abs uu____1472 uu____1507 ret1)))
in (

let uu____1529 = (

let uu____1530 = (mk_all_implicit binders)
in (

let uu____1537 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append uu____1530 uu____1537)))
in (FStar_Syntax_Util.abs uu____1529 body ret1)))))))))
in (

let c_push1 = (

let uu____1569 = (mk_lid "push")
in (register env1 uu____1569 c_push))
in (

let ret_tot_wp_a = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot wp_a1))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1593 = (

let uu____1594 = (

let uu____1611 = (args_of_binders1 binders)
in ((c), (uu____1611)))
in FStar_Syntax_Syntax.Tm_app (uu____1594))
in (mk1 uu____1593))
end
| uu____1634 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (

let uu____1639 = (

let uu____1640 = (

let uu____1649 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (

let uu____1656 = (

let uu____1665 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (uu____1665)::[])
in (uu____1649)::uu____1656))
in (

let uu____1690 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____1640 uu____1690)))
in (FStar_Syntax_Syntax.mk_Total uu____1639))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let uu____1694 = (

let uu____1695 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(c)::[]))
in (FStar_List.append binders uu____1695))
in (

let uu____1710 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____1714 = (

let uu____1717 = (

let uu____1728 = (

let uu____1731 = (

let uu____1732 = (

let uu____1743 = (

let uu____1752 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg uu____1752))
in (uu____1743)::[])
in (FStar_Syntax_Util.mk_app l_ite uu____1732))
in (uu____1731)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1728))
in (FStar_Syntax_Util.mk_app c_lift21 uu____1717))
in (FStar_Syntax_Util.ascribe uu____1714 ((FStar_Util.Inr (result_comp)), (FStar_Pervasives_Native.None)))))
in (FStar_Syntax_Util.abs uu____1694 uu____1710 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp result_comp))))))))
in (

let wp_if_then_else1 = (

let uu____1796 = (mk_lid "wp_if_then_else")
in (register env1 uu____1796 wp_if_then_else))
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

let uu____1809 = (

let uu____1820 = (

let uu____1823 = (

let uu____1824 = (

let uu____1835 = (

let uu____1838 = (

let uu____1839 = (

let uu____1850 = (

let uu____1859 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1859))
in (uu____1850)::[])
in (FStar_Syntax_Util.mk_app l_and uu____1839))
in (uu____1838)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1835))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1824))
in (

let uu____1884 = (

let uu____1887 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1887)::[])
in (uu____1823)::uu____1884))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1820))
in (FStar_Syntax_Util.mk_app c_app1 uu____1809))
in (

let uu____1896 = (

let uu____1897 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1897))
in (FStar_Syntax_Util.abs uu____1896 body ret_tot_wp_a))))))
in (

let wp_assert1 = (

let uu____1913 = (mk_lid "wp_assert")
in (register env1 uu____1913 wp_assert))
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

let uu____1926 = (

let uu____1937 = (

let uu____1940 = (

let uu____1941 = (

let uu____1952 = (

let uu____1955 = (

let uu____1956 = (

let uu____1967 = (

let uu____1976 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1976))
in (uu____1967)::[])
in (FStar_Syntax_Util.mk_app l_imp uu____1956))
in (uu____1955)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1952))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1941))
in (

let uu____2001 = (

let uu____2004 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____2004)::[])
in (uu____1940)::uu____2001))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1937))
in (FStar_Syntax_Util.mk_app c_app1 uu____1926))
in (

let uu____2013 = (

let uu____2014 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____2014))
in (FStar_Syntax_Util.abs uu____2013 body ret_tot_wp_a))))))
in (

let wp_assume1 = (

let uu____2030 = (mk_lid "wp_assume")
in (register env1 uu____2030 wp_assume))
in (

let wp_assume2 = (mk_generic_app wp_assume1)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____2041 = (

let uu____2050 = (

let uu____2057 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____2057))
in (uu____2050)::[])
in (

let uu____2070 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____2041 uu____2070)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let body = (

let uu____2077 = (

let uu____2088 = (

let uu____2091 = (

let uu____2092 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure1 uu____2092))
in (

let uu____2111 = (

let uu____2114 = (

let uu____2115 = (

let uu____2126 = (

let uu____2129 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____2129)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2126))
in (FStar_Syntax_Util.mk_app c_push1 uu____2115))
in (uu____2114)::[])
in (uu____2091)::uu____2111))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2088))
in (FStar_Syntax_Util.mk_app c_app1 uu____2077))
in (

let uu____2146 = (

let uu____2147 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(b)::(f)::[]))
in (FStar_List.append binders uu____2147))
in (FStar_Syntax_Util.abs uu____2146 body ret_tot_wp_a))))))
in (

let wp_close1 = (

let uu____2163 = (mk_lid "wp_close")
in (register env1 uu____2163 wp_close))
in (

let wp_close2 = (mk_generic_app wp_close1)
in (

let ret_tot_type = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype))
in (

let ret_gtot_type = (

let uu____2173 = (

let uu____2174 = (

let uu____2175 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____2175))
in (FStar_Syntax_Util.residual_comp_of_lcomp uu____2174))
in FStar_Pervasives_Native.Some (uu____2173))
in (

let mk_forall1 = (fun x body -> (

let uu____2187 = (

let uu____2194 = (

let uu____2195 = (

let uu____2212 = (

let uu____2223 = (

let uu____2232 = (

let uu____2233 = (

let uu____2234 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2234)::[])
in (FStar_Syntax_Util.abs uu____2233 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg uu____2232))
in (uu____2223)::[])
in ((FStar_Syntax_Util.tforall), (uu____2212)))
in FStar_Syntax_Syntax.Tm_app (uu____2195))
in (FStar_Syntax_Syntax.mk uu____2194))
in (uu____2187 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (

let uu____2294 = (

let uu____2295 = (FStar_Syntax_Subst.compress t)
in uu____2295.FStar_Syntax_Syntax.n)
in (match (uu____2294) with
| FStar_Syntax_Syntax.Tm_type (uu____2298) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2330 -> (match (uu____2330) with
| (b, uu____2338) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____2343 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____2354 = (

let uu____2355 = (FStar_Syntax_Subst.compress t)
in uu____2355.FStar_Syntax_Syntax.n)
in (match (uu____2354) with
| FStar_Syntax_Syntax.Tm_type (uu____2358) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2390 -> (match (uu____2390) with
| (b, uu____2398) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____2403 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel1 = (mk_rel rel)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t)
in (

let uu____2477 = (

let uu____2478 = (FStar_Syntax_Subst.compress t1)
in uu____2478.FStar_Syntax_Syntax.n)
in (match (uu____2477) with
| FStar_Syntax_Syntax.Tm_type (uu____2483) -> begin
(rel x y)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____2486); FStar_Syntax_Syntax.pos = uu____2487; FStar_Syntax_Syntax.vars = uu____2488}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2532 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2532) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2539 = (

let uu____2542 = (

let uu____2553 = (

let uu____2562 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2562))
in (uu____2553)::[])
in (FStar_Syntax_Util.mk_app x uu____2542))
in (

let uu____2579 = (

let uu____2582 = (

let uu____2593 = (

let uu____2602 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2602))
in (uu____2593)::[])
in (FStar_Syntax_Util.mk_app y uu____2582))
in (mk_rel1 b uu____2539 uu____2579)))
in (mk_forall1 a11 body)))
end
| uu____2619 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2623 = (

let uu____2626 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2629 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2626 uu____2629)))
in (

let uu____2632 = (

let uu____2635 = (

let uu____2638 = (

let uu____2649 = (

let uu____2658 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2658))
in (uu____2649)::[])
in (FStar_Syntax_Util.mk_app x uu____2638))
in (

let uu____2675 = (

let uu____2678 = (

let uu____2689 = (

let uu____2698 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____2698))
in (uu____2689)::[])
in (FStar_Syntax_Util.mk_app y uu____2678))
in (mk_rel1 b uu____2635 uu____2675)))
in (FStar_Syntax_Util.mk_imp uu____2623 uu____2632)))
in (

let uu____2715 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____2715)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____2718); FStar_Syntax_Syntax.pos = uu____2719; FStar_Syntax_Syntax.vars = uu____2720}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2764 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2764) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2771 = (

let uu____2774 = (

let uu____2785 = (

let uu____2794 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2794))
in (uu____2785)::[])
in (FStar_Syntax_Util.mk_app x uu____2774))
in (

let uu____2811 = (

let uu____2814 = (

let uu____2825 = (

let uu____2834 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2834))
in (uu____2825)::[])
in (FStar_Syntax_Util.mk_app y uu____2814))
in (mk_rel1 b uu____2771 uu____2811)))
in (mk_forall1 a11 body)))
end
| uu____2851 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2855 = (

let uu____2858 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2861 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2858 uu____2861)))
in (

let uu____2864 = (

let uu____2867 = (

let uu____2870 = (

let uu____2881 = (

let uu____2890 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2890))
in (uu____2881)::[])
in (FStar_Syntax_Util.mk_app x uu____2870))
in (

let uu____2907 = (

let uu____2910 = (

let uu____2921 = (

let uu____2930 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____2930))
in (uu____2921)::[])
in (FStar_Syntax_Util.mk_app y uu____2910))
in (mk_rel1 b uu____2867 uu____2907)))
in (FStar_Syntax_Util.mk_imp uu____2855 uu____2864)))
in (

let uu____2947 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____2947)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders1, comp) -> begin
(

let t2 = (

let uu___363_2986 = t1
in (

let uu____2987 = (

let uu____2988 = (

let uu____3003 = (

let uu____3006 = (FStar_Syntax_Util.arrow binders1 comp)
in (FStar_Syntax_Syntax.mk_Total uu____3006))
in (((binder)::[]), (uu____3003)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2988))
in {FStar_Syntax_Syntax.n = uu____2987; FStar_Syntax_Syntax.pos = uu___363_2986.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___363_2986.FStar_Syntax_Syntax.vars}))
in (mk_rel1 t2 x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3029) -> begin
(failwith "unhandled arrow")
end
| uu____3046 -> begin
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

let uu____3081 = (

let uu____3082 = (FStar_Syntax_Subst.compress t1)
in uu____3082.FStar_Syntax_Syntax.n)
in (match (uu____3081) with
| FStar_Syntax_Syntax.Tm_type (uu____3085) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when (

let uu____3112 = (FStar_Syntax_Subst.compress head1)
in (FStar_Syntax_Util.is_tuple_constructor uu____3112)) -> begin
(

let project = (fun i tuple -> (

let projector = (

let uu____3131 = (

let uu____3132 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env1 uu____3132 i))
in (FStar_Syntax_Syntax.fvar uu____3131 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (FStar_Pervasives_Native.None)))::[]))))
in (

let uu____3161 = (

let uu____3172 = (FStar_List.mapi (fun i uu____3190 -> (match (uu____3190) with
| (t2, q) -> begin
(

let uu____3209 = (project i x)
in (

let uu____3212 = (project i y)
in (mk_stronger t2 uu____3209 uu____3212)))
end)) args)
in (match (uu____3172) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____3161) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____3265); FStar_Syntax_Syntax.pos = uu____3266; FStar_Syntax_Syntax.vars = uu____3267}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____3311 -> (match (uu____3311) with
| (bv, q) -> begin
(

let uu____3324 = (

let uu____3325 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____3325))
in (FStar_Syntax_Syntax.gen_bv uu____3324 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____3332 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____3332))) bvs)
in (

let body = (

let uu____3334 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____3337 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____3334 uu____3337)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____3346); FStar_Syntax_Syntax.pos = uu____3347; FStar_Syntax_Syntax.vars = uu____3348}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____3392 -> (match (uu____3392) with
| (bv, q) -> begin
(

let uu____3405 = (

let uu____3406 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____3406))
in (FStar_Syntax_Syntax.gen_bv uu____3405 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____3413 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____3413))) bvs)
in (

let body = (

let uu____3415 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____3418 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____3415 uu____3418)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| uu____3425 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (

let uu____3427 = (FStar_Syntax_Util.unascribe wp_a1)
in (

let uu____3430 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (

let uu____3433 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger uu____3427 uu____3430 uu____3433))))
in (

let uu____3436 = (

let uu____3437 = (binders_of_list1 ((((a1), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders uu____3437))
in (FStar_Syntax_Util.abs uu____3436 body ret_tot_type))))))
in (

let stronger1 = (

let uu____3469 = (mk_lid "stronger")
in (register env1 uu____3469 stronger))
in (

let stronger2 = (mk_generic_app stronger1)
in (

let ite_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3475 = (FStar_Util.prefix gamma)
in (match (uu____3475) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv1 = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq1 = (

let uu____3540 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm uu____3540))
in (

let uu____3545 = (FStar_Syntax_Util.destruct_typ_as_formula eq1)
in (match (uu____3545) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (binders1, [], body)) -> begin
(

let k_app = (

let uu____3555 = (args_of_binders1 binders1)
in (FStar_Syntax_Util.mk_app k_tm uu____3555))
in (

let guard_free1 = (

let uu____3567 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.guard_free FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3567))
in (

let pat = (

let uu____3571 = (

let uu____3582 = (FStar_Syntax_Syntax.as_arg k_app)
in (uu____3582)::[])
in (FStar_Syntax_Util.mk_app guard_free1 uu____3571))
in (

let pattern_guarded_body = (

let uu____3610 = (

let uu____3611 = (

let uu____3618 = (

let uu____3619 = (

let uu____3632 = (

let uu____3643 = (FStar_Syntax_Syntax.as_arg pat)
in (uu____3643)::[])
in (uu____3632)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____3619))
in ((body), (uu____3618)))
in FStar_Syntax_Syntax.Tm_meta (uu____3611))
in (mk1 uu____3610))
in (FStar_Syntax_Util.close_forall_no_univs binders1 pattern_guarded_body)))))
end
| uu____3690 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (

let uu____3698 = (

let uu____3701 = (

let uu____3702 = (

let uu____3705 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____3708 = (

let uu____3719 = (args_of_binders1 wp_args)
in (

let uu____3722 = (

let uu____3725 = (

let uu____3726 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg uu____3726))
in (uu____3725)::[])
in (FStar_List.append uu____3719 uu____3722)))
in (FStar_Syntax_Util.mk_app uu____3705 uu____3708)))
in (FStar_Syntax_Util.mk_imp equiv1 uu____3702))
in (FStar_Syntax_Util.mk_forall_no_univ k uu____3701))
in (FStar_Syntax_Util.abs gamma uu____3698 ret_gtot_type))
in (

let uu____3727 = (

let uu____3728 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____3728))
in (FStar_Syntax_Util.abs uu____3727 body ret_gtot_type)))))
end)))
in (

let ite_wp1 = (

let uu____3744 = (mk_lid "ite_wp")
in (register env1 uu____3744 ite_wp))
in (

let ite_wp2 = (mk_generic_app ite_wp1)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3750 = (FStar_Util.prefix gamma)
in (match (uu____3750) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let body = (

let uu____3807 = (

let uu____3808 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (

let uu____3815 = (

let uu____3826 = (

let uu____3835 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____3835))
in (uu____3826)::[])
in (FStar_Syntax_Util.mk_app uu____3808 uu____3815)))
in (FStar_Syntax_Util.mk_forall_no_univ x uu____3807))
in (

let uu____3852 = (

let uu____3853 = (

let uu____3862 = (FStar_Syntax_Syntax.binders_of_list ((a1)::[]))
in (FStar_List.append uu____3862 gamma))
in (FStar_List.append binders uu____3853))
in (FStar_Syntax_Util.abs uu____3852 body ret_gtot_type))))
end)))
in (

let null_wp1 = (

let uu____3884 = (mk_lid "null_wp")
in (register env1 uu____3884 null_wp))
in (

let null_wp2 = (mk_generic_app null_wp1)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let body = (

let uu____3895 = (

let uu____3906 = (

let uu____3909 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3910 = (

let uu____3913 = (

let uu____3914 = (

let uu____3925 = (

let uu____3934 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____3934))
in (uu____3925)::[])
in (FStar_Syntax_Util.mk_app null_wp2 uu____3914))
in (

let uu____3951 = (

let uu____3954 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____3954)::[])
in (uu____3913)::uu____3951))
in (uu____3909)::uu____3910))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____3906))
in (FStar_Syntax_Util.mk_app stronger2 uu____3895))
in (

let uu____3963 = (

let uu____3964 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____3964))
in (FStar_Syntax_Util.abs uu____3963 body ret_tot_type))))
in (

let wp_trivial1 = (

let uu____3980 = (mk_lid "wp_trivial")
in (register env1 uu____3980 wp_trivial))
in (

let wp_trivial2 = (mk_generic_app wp_trivial1)
in ((

let uu____3985 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3985) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____3986 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (

let uu____3992 = (

let uu____3993 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____3993))
in (

let uu____4041 = (

let uu___364_4042 = ed
in (

let uu____4043 = (

let uu____4044 = (c wp_if_then_else2)
in (([]), (uu____4044)))
in (

let uu____4051 = (

let uu____4052 = (c ite_wp2)
in (([]), (uu____4052)))
in (

let uu____4059 = (

let uu____4060 = (c stronger2)
in (([]), (uu____4060)))
in (

let uu____4067 = (

let uu____4068 = (c wp_close2)
in (([]), (uu____4068)))
in (

let uu____4075 = (

let uu____4076 = (c wp_assert2)
in (([]), (uu____4076)))
in (

let uu____4083 = (

let uu____4084 = (c wp_assume2)
in (([]), (uu____4084)))
in (

let uu____4091 = (

let uu____4092 = (c null_wp2)
in (([]), (uu____4092)))
in (

let uu____4099 = (

let uu____4100 = (c wp_trivial2)
in (([]), (uu____4100)))
in {FStar_Syntax_Syntax.cattributes = uu___364_4042.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___364_4042.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___364_4042.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___364_4042.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___364_4042.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___364_4042.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___364_4042.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu____4043; FStar_Syntax_Syntax.ite_wp = uu____4051; FStar_Syntax_Syntax.stronger = uu____4059; FStar_Syntax_Syntax.close_wp = uu____4067; FStar_Syntax_Syntax.assert_p = uu____4075; FStar_Syntax_Syntax.assume_p = uu____4083; FStar_Syntax_Syntax.null_wp = uu____4091; FStar_Syntax_Syntax.trivial = uu____4099; FStar_Syntax_Syntax.repr = uu___364_4042.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___364_4042.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___364_4042.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___364_4042.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___364_4042.FStar_Syntax_Syntax.eff_attrs})))))))))
in ((uu____3992), (uu____4041)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.tcenv)


let set_env : env  ->  FStar_TypeChecker_Env.env  ->  env = (fun dmff_env env' -> (

let uu___365_4122 = dmff_env
in {tcenv = env'; subst = uu___365_4122.subst; tc_const = uu___365_4122.tc_const}))

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____4139 -> begin
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
| uu____4153 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  nm = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____4171) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c1) when (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___351_4184 -> (match (uu___351_4184) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____4185 -> begin
false
end)))) -> begin
M (c1.FStar_Syntax_Syntax.result_typ)
end
| uu____4186 -> begin
(

let uu____4187 = (

let uu____4192 = (

let uu____4193 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s" uu____4193))
in ((FStar_Errors.Error_UnexpectedDM4FType), (uu____4192)))
in (FStar_Errors.raise_error uu____4187 c.FStar_Syntax_Syntax.pos))
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___352_4198 -> (match (uu___352_4198) with
| N (t) -> begin
(

let uu____4200 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" uu____4200))
end
| M (t) -> begin
(

let uu____4202 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" uu____4202))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n1 -> (match (n1) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4208, c) -> begin
(nm_of_comp c)
end
| uu____4230 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (

let uu____4240 = (nm_of_comp c)
in (match (uu____4240) with
| M (uu____4241) -> begin
true
end
| N (uu____4242) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____4248 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ1 -> (

let uu____4262 = (

let uu____4271 = (

let uu____4278 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4278))
in (uu____4271)::[])
in (

let uu____4297 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____4262 uu____4297))))
in (

let uu____4300 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once uu____4300))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun mk1 env a -> (

let uu____4341 = (

let uu____4342 = (

let uu____4357 = (

let uu____4366 = (

let uu____4373 = (

let uu____4374 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv uu____4374))
in (

let uu____4375 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4373), (uu____4375))))
in (uu____4366)::[])
in (

let uu____4392 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____4357), (uu____4392))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4342))
in (mk1 uu____4341)))
and star_type' : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type1 = (mk_star_to_type mk1)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____4432) -> begin
(

let binders1 = (FStar_List.map (fun uu____4478 -> (match (uu____4478) with
| (bv, aqual) -> begin
(

let uu____4497 = (

let uu___366_4498 = bv
in (

let uu____4499 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___366_4498.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___366_4498.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4499}))
in ((uu____4497), (aqual)))
end)) binders)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4504, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____4506); FStar_Syntax_Syntax.pos = uu____4507; FStar_Syntax_Syntax.vars = uu____4508}) -> begin
(

let uu____4537 = (

let uu____4538 = (

let uu____4553 = (

let uu____4556 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal uu____4556))
in ((binders1), (uu____4553)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4538))
in (mk1 uu____4537))
end
| uu____4567 -> begin
(

let uu____4568 = (is_monadic_arrow t1.FStar_Syntax_Syntax.n)
in (match (uu____4568) with
| N (hn) -> begin
(

let uu____4570 = (

let uu____4571 = (

let uu____4586 = (

let uu____4589 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total uu____4589))
in ((binders1), (uu____4586)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4571))
in (mk1 uu____4570))
end
| M (a) -> begin
(

let uu____4601 = (

let uu____4602 = (

let uu____4617 = (

let uu____4626 = (

let uu____4635 = (

let uu____4642 = (

let uu____4643 = (mk_star_to_type1 env a)
in (FStar_Syntax_Syntax.null_bv uu____4643))
in (

let uu____4644 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4642), (uu____4644))))
in (uu____4635)::[])
in (FStar_List.append binders1 uu____4626))
in (

let uu____4667 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____4617), (uu____4667))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4602))
in (mk1 uu____4601))
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

let uu____4755 = (f x)
in (FStar_Util.string_builder_append strb uu____4755));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____4762 = (f x1)
in (FStar_Util.string_builder_append strb uu____4762));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (

let uu____4764 = (

let uu____4769 = (

let uu____4770 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____4771 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.format2 "Dependency found in term %s : %s" uu____4770 uu____4771)))
in ((FStar_Errors.Warning_DependencyFound), (uu____4769)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4764))))
in (

let rec is_non_dependent_arrow = (fun ty n1 -> (

let uu____4787 = (

let uu____4788 = (FStar_Syntax_Subst.compress ty)
in uu____4788.FStar_Syntax_Syntax.n)
in (match (uu____4787) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____4813 = (

let uu____4814 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (not (uu____4814)))
in (match (uu____4813) with
| true -> begin
false
end
| uu____4815 -> begin
(FStar_All.try_with (fun uu___368_4825 -> (match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty1 -> (

let sinter = (

let uu____4848 = (FStar_Syntax_Free.names ty1)
in (FStar_Util.set_intersect uu____4848 s))
in (

let uu____4851 = (

let uu____4852 = (FStar_Util.set_is_empty sinter)
in (not (uu____4852)))
in (match (uu____4851) with
| true -> begin
((debug1 ty1 sinter);
(FStar_Exn.raise Not_found);
)
end
| uu____4854 -> begin
()
end))))
in (

let uu____4855 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____4855) with
| (binders1, c1) -> begin
(

let s = (FStar_List.fold_left (fun s uu____4879 -> (match (uu____4879) with
| (bv, uu____4891) -> begin
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
| uu____4908 -> begin
true
end));
)))
end)))
end)) (fun uu___367_4910 -> (match (uu___367_4910) with
| Not_found -> begin
false
end)))
end))
end
| uu____4911 -> begin
((

let uu____4913 = (

let uu____4918 = (

let uu____4919 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format1 "Not a dependent arrow : %s" uu____4919))
in ((FStar_Errors.Warning_NotDependentArrow), (uu____4918)))
in (FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos uu____4913));
false;
)
end)))
in (

let rec is_valid_application = (fun head2 -> (

let uu____4930 = (

let uu____4931 = (FStar_Syntax_Subst.compress head2)
in uu____4931.FStar_Syntax_Syntax.n)
in (match (uu____4930) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (

let uu____4936 = (FStar_Syntax_Subst.compress head2)
in (FStar_Syntax_Util.is_tuple_constructor uu____4936))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4938 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4938) with
| ((uu____4947, ty), uu____4949) -> begin
(

let uu____4954 = (is_non_dependent_arrow ty (FStar_List.length args))
in (match (uu____4954) with
| true -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env.tcenv t1)
in (

let uu____4964 = (

let uu____4965 = (FStar_Syntax_Subst.compress res)
in uu____4965.FStar_Syntax_Syntax.n)
in (match (uu____4964) with
| FStar_Syntax_Syntax.Tm_app (uu____4968) -> begin
true
end
| uu____4985 -> begin
((

let uu____4987 = (

let uu____4992 = (

let uu____4993 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format1 "Got a term which might be a non-dependent user-defined data-type %s\n" uu____4993))
in ((FStar_Errors.Warning_NondependentUserDefinedDataType), (uu____4992)))
in (FStar_Errors.log_issue head2.FStar_Syntax_Syntax.pos uu____4987));
false;
)
end)))
end
| uu____4994 -> begin
false
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____4995) -> begin
true
end
| FStar_Syntax_Syntax.Tm_name (uu____4996) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____4998) -> begin
(is_valid_application t2)
end
| uu____5003 -> begin
false
end)))
in (

let uu____5004 = (is_valid_application head1)
in (match (uu____5004) with
| true -> begin
(

let uu____5005 = (

let uu____5006 = (

let uu____5023 = (FStar_List.map (fun uu____5052 -> (match (uu____5052) with
| (t2, qual) -> begin
(

let uu____5077 = (star_type' env t2)
in ((uu____5077), (qual)))
end)) args)
in ((head1), (uu____5023)))
in FStar_Syntax_Syntax.Tm_app (uu____5006))
in (mk1 uu____5005))
end
| uu____5092 -> begin
(

let uu____5093 = (

let uu____5098 = (

let uu____5099 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" uu____5099))
in ((FStar_Errors.Fatal_WrongTerm), (uu____5098)))
in (FStar_Errors.raise_err uu____5093))
end)))))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5100) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____5101) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____5102) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5103) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____5131 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____5131) with
| (binders1, repr1) -> begin
(

let env1 = (

let uu___369_5139 = env
in (

let uu____5140 = (FStar_TypeChecker_Env.push_binders env.tcenv binders1)
in {tcenv = uu____5140; subst = uu___369_5139.subst; tc_const = uu___369_5139.tc_const}))
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

let uu___370_5162 = x1
in {FStar_Syntax_Syntax.ppname = uu___370_5162.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___370_5162.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t5))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____5169 = (

let uu____5170 = (

let uu____5177 = (star_type' env t2)
in ((uu____5177), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____5170))
in (mk1 uu____5169))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inl (t2), FStar_Pervasives_Native.None), something) -> begin
(

let uu____5229 = (

let uu____5230 = (

let uu____5257 = (star_type' env e)
in (

let uu____5260 = (

let uu____5277 = (

let uu____5286 = (star_type' env t2)
in FStar_Util.Inl (uu____5286))
in ((uu____5277), (FStar_Pervasives_Native.None)))
in ((uu____5257), (uu____5260), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5230))
in (mk1 uu____5229))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), FStar_Pervasives_Native.None), something) -> begin
(

let uu____5374 = (

let uu____5375 = (

let uu____5402 = (star_type' env e)
in (

let uu____5405 = (

let uu____5422 = (

let uu____5431 = (star_type' env (FStar_Syntax_Util.comp_result c))
in FStar_Util.Inl (uu____5431))
in ((uu____5422), (FStar_Pervasives_Native.None)))
in ((uu____5402), (uu____5405), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5375))
in (mk1 uu____5374))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5472, (uu____5473, FStar_Pervasives_Native.Some (uu____5474)), uu____5475) -> begin
(

let uu____5524 = (

let uu____5529 = (

let uu____5530 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Ascriptions with tactics are outside of the definition language: %s" uu____5530))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5529)))
in (FStar_Errors.raise_err uu____5524))
end
| FStar_Syntax_Syntax.Tm_refine (uu____5531) -> begin
(

let uu____5538 = (

let uu____5543 = (

let uu____5544 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" uu____5544))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5543)))
in (FStar_Errors.raise_err uu____5538))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____5545) -> begin
(

let uu____5552 = (

let uu____5557 = (

let uu____5558 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" uu____5558))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5557)))
in (FStar_Errors.raise_err uu____5552))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5559) -> begin
(

let uu____5566 = (

let uu____5571 = (

let uu____5572 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_quoted is outside of the definition language: %s" uu____5572))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5571)))
in (FStar_Errors.raise_err uu____5566))
end
| FStar_Syntax_Syntax.Tm_constant (uu____5573) -> begin
(

let uu____5574 = (

let uu____5579 = (

let uu____5580 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" uu____5580))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5579)))
in (FStar_Errors.raise_err uu____5574))
end
| FStar_Syntax_Syntax.Tm_match (uu____5581) -> begin
(

let uu____5604 = (

let uu____5609 = (

let uu____5610 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" uu____5610))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5609)))
in (FStar_Errors.raise_err uu____5604))
end
| FStar_Syntax_Syntax.Tm_let (uu____5611) -> begin
(

let uu____5624 = (

let uu____5629 = (

let uu____5630 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" uu____5630))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5629)))
in (FStar_Errors.raise_err uu____5624))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5631) -> begin
(

let uu____5644 = (

let uu____5649 = (

let uu____5650 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" uu____5650))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5649)))
in (FStar_Errors.raise_err uu____5644))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5651 = (

let uu____5656 = (

let uu____5657 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" uu____5657))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____5656)))
in (FStar_Errors.raise_err uu____5651))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5659 = (FStar_Syntax_Util.unfold_lazy i)
in (star_type' env uu____5659))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5662) -> begin
(failwith "impossible")
end)))))


let is_monadic : FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___354_5691 -> (match (uu___354_5691) with
| FStar_Pervasives_Native.None -> begin
(failwith "un-annotated lambda?!")
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___353_5698 -> (match (uu___353_5698) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____5699 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____5705 = (

let uu____5706 = (FStar_Syntax_Subst.compress t)
in uu____5706.FStar_Syntax_Syntax.n)
in (match (uu____5705) with
| FStar_Syntax_Syntax.Tm_app (head1, args) when (FStar_Syntax_Util.is_tuple_constructor head1) -> begin
(

let r = (

let uu____5736 = (

let uu____5737 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5737))
in (is_C uu____5736))
in (match (r) with
| true -> begin
((

let uu____5759 = (

let uu____5760 = (FStar_List.for_all (fun uu____5770 -> (match (uu____5770) with
| (h, uu____5778) -> begin
(is_C h)
end)) args)
in (not (uu____5760)))
in (match (uu____5759) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____5783 -> begin
()
end));
true;
)
end
| uu____5784 -> begin
((

let uu____5786 = (

let uu____5787 = (FStar_List.for_all (fun uu____5798 -> (match (uu____5798) with
| (h, uu____5806) -> begin
(

let uu____5811 = (is_C h)
in (not (uu____5811)))
end)) args)
in (not (uu____5787)))
in (match (uu____5786) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____5812 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____5835 = (nm_of_comp comp)
in (match (uu____5835) with
| M (t1) -> begin
((

let uu____5838 = (is_C t1)
in (match (uu____5838) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____5839 -> begin
()
end));
true;
)
end
| N (t1) -> begin
(is_C t1)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5842) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5848) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____5854, uu____5855) -> begin
(is_C t1)
end
| uu____5896 -> begin
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

let uu____5929 = (

let uu____5930 = (

let uu____5947 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5950 = (

let uu____5961 = (

let uu____5970 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (uu____5970)))
in (uu____5961)::[])
in ((uu____5947), (uu____5950))))
in FStar_Syntax_Syntax.Tm_app (uu____5930))
in (mk1 uu____5929))
in (

let uu____6005 = (

let uu____6006 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____6006)::[])
in (FStar_Syntax_Util.abs uu____6005 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___355_6029 -> (match (uu___355_6029) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____6030 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let return_if = (fun uu____6265 -> (match (uu____6265) with
| (rec_nm, s_e, u_e) -> begin
(

let check1 = (fun t1 t2 -> (

let uu____6302 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (

let uu____6304 = (

let uu____6305 = (FStar_TypeChecker_Rel.teq env.tcenv t1 t2)
in (FStar_TypeChecker_Env.is_trivial uu____6305))
in (not (uu____6304))))
in (match (uu____6302) with
| true -> begin
(

let uu____6306 = (

let uu____6311 = (

let uu____6312 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6313 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6314 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" uu____6312 uu____6313 uu____6314))))
in ((FStar_Errors.Fatal_TypeMismatch), (uu____6311)))
in (FStar_Errors.raise_err uu____6306))
end
| uu____6315 -> begin
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

let uu____6335 = (mk_return env t1 s_e)
in ((M (t1)), (uu____6335), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(

let uu____6342 = (

let uu____6347 = (

let uu____6348 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____6349 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6350 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" uu____6348 uu____6349 uu____6350))))
in ((FStar_Errors.Fatal_EffectfulAndPureComputationMismatch), (uu____6347)))
in (FStar_Errors.raise_err uu____6342))
end))
end))
in (

let ensure_m = (fun env1 e2 -> (

let strip_m = (fun uu___356_6399 -> (match (uu___356_6399) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____6415 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(

let uu____6435 = (

let uu____6440 = (

let uu____6441 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " uu____6441))
in ((FStar_Errors.Fatal_LetBoundMonadicMismatch), (uu____6440)))
in (FStar_Errors.raise_error uu____6435 e2.FStar_Syntax_Syntax.pos))
end
| M (uu____6448) -> begin
(

let uu____6449 = (check env1 e2 context_nm)
in (strip_m uu____6449))
end)))
in (

let uu____6456 = (

let uu____6457 = (FStar_Syntax_Subst.compress e)
in uu____6457.FStar_Syntax_Syntax.n)
in (match (uu____6456) with
| FStar_Syntax_Syntax.Tm_bvar (uu____6466) -> begin
(

let uu____6467 = (infer env e)
in (return_if uu____6467))
end
| FStar_Syntax_Syntax.Tm_name (uu____6474) -> begin
(

let uu____6475 = (infer env e)
in (return_if uu____6475))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____6482) -> begin
(

let uu____6483 = (infer env e)
in (return_if uu____6483))
end
| FStar_Syntax_Syntax.Tm_abs (uu____6490) -> begin
(

let uu____6509 = (infer env e)
in (return_if uu____6509))
end
| FStar_Syntax_Syntax.Tm_constant (uu____6516) -> begin
(

let uu____6517 = (infer env e)
in (return_if uu____6517))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____6524) -> begin
(

let uu____6531 = (infer env e)
in (return_if uu____6531))
end
| FStar_Syntax_Syntax.Tm_app (uu____6538) -> begin
(

let uu____6555 = (infer env e)
in (return_if uu____6555))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6563 = (FStar_Syntax_Util.unfold_lazy i)
in (check env uu____6563 context_nm))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env1 e21 -> (check env1 e21 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env1 body -> (check env1 body context_nm)))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____6625) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____6631) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____6637, uu____6638) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____6679) -> begin
(

let uu____6692 = (

let uu____6693 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" uu____6693))
in (failwith uu____6692))
end
| FStar_Syntax_Syntax.Tm_type (uu____6700) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____6707) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____6728) -> begin
(

let uu____6735 = (

let uu____6736 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" uu____6736))
in (failwith uu____6735))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____6743) -> begin
(

let uu____6756 = (

let uu____6757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" uu____6757))
in (failwith uu____6756))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____6764) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6793 = (

let uu____6794 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" uu____6794))
in (failwith uu____6793))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let normalize1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::[]) env.tcenv)
in (

let uu____6822 = (

let uu____6823 = (FStar_Syntax_Subst.compress e)
in uu____6823.FStar_Syntax_Syntax.n)
in (match (uu____6822) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6841 = (FStar_Syntax_Util.unfold_lazy i)
in (infer env uu____6841))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) -> begin
(

let subst_rc_opt = (fun subst1 rc_opt1 -> (match (rc_opt1) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = uu____6892; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = uu____6893}) -> begin
rc_opt1
end
| FStar_Pervasives_Native.None -> begin
rc_opt1
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____6899 = (

let uu___371_6900 = rc
in (

let uu____6901 = (

let uu____6906 = (

let uu____6909 = (FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ)
in (FStar_Syntax_Subst.subst subst1 uu____6909))
in FStar_Pervasives_Native.Some (uu____6906))
in {FStar_Syntax_Syntax.residual_effect = uu___371_6900.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6901; FStar_Syntax_Syntax.residual_flags = uu___371_6900.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____6899))
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

let uu___372_6921 = env
in (

let uu____6922 = (FStar_TypeChecker_Env.push_binders env.tcenv binders1)
in {tcenv = uu____6922; subst = uu___372_6921.subst; tc_const = uu___372_6921.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____6948 -> (match (uu____6948) with
| (bv, qual) -> begin
(

let sort = (star_type' env1 bv.FStar_Syntax_Syntax.sort)
in (((

let uu___373_6971 = bv
in {FStar_Syntax_Syntax.ppname = uu___373_6971.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___373_6971.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders1)
in (

let uu____6972 = (FStar_List.fold_left (fun uu____7003 uu____7004 -> (match (((uu____7003), (uu____7004))) with
| ((env2, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____7062 = (is_C c)
in (match (uu____7062) with
| true -> begin
(

let xw = (

let uu____7070 = (star_type' env2 c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w") FStar_Pervasives_Native.None uu____7070))
in (

let x = (

let uu___374_7072 = bv
in (

let uu____7073 = (

let uu____7076 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env2 c uu____7076))
in {FStar_Syntax_Syntax.ppname = uu___374_7072.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___374_7072.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7073}))
in (

let env3 = (

let uu___375_7078 = env2
in (

let uu____7079 = (

let uu____7082 = (

let uu____7083 = (

let uu____7090 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (uu____7090)))
in FStar_Syntax_Syntax.NT (uu____7083))
in (uu____7082)::env2.subst)
in {tcenv = uu___375_7078.tcenv; subst = uu____7079; tc_const = uu___375_7078.tc_const}))
in (

let uu____7095 = (

let uu____7098 = (FStar_Syntax_Syntax.mk_binder x)
in (

let uu____7099 = (

let uu____7102 = (FStar_Syntax_Syntax.mk_binder xw)
in (uu____7102)::acc)
in (uu____7098)::uu____7099))
in ((env3), (uu____7095))))))
end
| uu____7105 -> begin
(

let x = (

let uu___376_7107 = bv
in (

let uu____7108 = (star_type' env2 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___376_7107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___376_7107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7108}))
in (

let uu____7111 = (

let uu____7114 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7114)::acc)
in ((env2), (uu____7111))))
end)))
end)) ((env1), ([])) binders1)
in (match (uu____6972) with
| (env2, u_binders) -> begin
(

let u_binders1 = (FStar_List.rev u_binders)
in (

let uu____7134 = (

let check_what = (

let uu____7160 = (is_monadic rc_opt1)
in (match (uu____7160) with
| true -> begin
check_m
end
| uu____7173 -> begin
check_n
end))
in (

let uu____7174 = (check_what env2 body1)
in (match (uu____7174) with
| (t, s_body, u_body) -> begin
(

let uu____7194 = (

let uu____7197 = (

let uu____7198 = (is_monadic rc_opt1)
in (match (uu____7198) with
| true -> begin
M (t)
end
| uu____7199 -> begin
N (t)
end))
in (comp_of_nm uu____7197))
in ((uu____7194), (s_body), (u_body)))
end)))
in (match (uu____7134) with
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

let uu____7235 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___357_7239 -> (match (uu___357_7239) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____7240 -> begin
false
end))))
in (match (uu____7235) with
| true -> begin
(

let uu____7241 = (FStar_List.filter (fun uu___358_7245 -> (match (uu___358_7245) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____7246 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None uu____7241))
end
| uu____7249 -> begin
rc
end))
in FStar_Pervasives_Native.Some (rc1))
end
| FStar_Pervasives_Native.Some (rt) -> begin
(

let uu____7255 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___359_7259 -> (match (uu___359_7259) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____7260 -> begin
false
end))))
in (match (uu____7255) with
| true -> begin
(

let flags1 = (FStar_List.filter (fun uu___360_7267 -> (match (uu___360_7267) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____7268 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____7269 = (

let uu____7270 = (

let uu____7275 = (double_star rt)
in FStar_Pervasives_Native.Some (uu____7275))
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid uu____7270 flags1))
in FStar_Pervasives_Native.Some (uu____7269)))
end
| uu____7280 -> begin
(

let uu____7281 = (

let uu___377_7282 = rc
in (

let uu____7283 = (

let uu____7288 = (star_type' env2 rt)
in FStar_Pervasives_Native.Some (uu____7288))
in {FStar_Syntax_Syntax.residual_effect = uu___377_7282.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____7283; FStar_Syntax_Syntax.residual_flags = uu___377_7282.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____7281))
end))
end)
end)
in (

let uu____7293 = (

let comp1 = (

let uu____7301 = (is_monadic rc_opt1)
in (

let uu____7302 = (FStar_Syntax_Subst.subst env2.subst s_body)
in (trans_G env2 (FStar_Syntax_Util.comp_result comp) uu____7301 uu____7302)))
in (

let uu____7303 = (FStar_Syntax_Util.ascribe u_body ((FStar_Util.Inr (comp1)), (FStar_Pervasives_Native.None)))
in ((uu____7303), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp1))))))
in (match (uu____7293) with
| (u_body1, u_rc_opt) -> begin
(

let s_body1 = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders1 = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (

let uu____7341 = (

let uu____7342 = (

let uu____7361 = (

let uu____7364 = (FStar_Syntax_Subst.closing_of_binders s_binders1)
in (subst_rc_opt uu____7364 s_rc_opt))
in ((s_binders1), (s_body1), (uu____7361)))
in FStar_Syntax_Syntax.Tm_abs (uu____7342))
in (mk1 uu____7341))
in (

let u_body2 = (FStar_Syntax_Subst.close u_binders1 u_body1)
in (

let u_binders2 = (FStar_Syntax_Subst.close_binders u_binders1)
in (

let u_term = (

let uu____7384 = (

let uu____7385 = (

let uu____7404 = (

let uu____7407 = (FStar_Syntax_Subst.closing_of_binders u_binders2)
in (subst_rc_opt uu____7407 u_rc_opt))
in ((u_binders2), (u_body2), (uu____7404)))
in FStar_Syntax_Syntax.Tm_abs (uu____7385))
in (mk1 uu____7384))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.p = uu____7423}; FStar_Syntax_Syntax.fv_delta = uu____7424; FStar_Syntax_Syntax.fv_qual = uu____7425}) -> begin
(

let uu____7428 = (

let uu____7433 = (FStar_TypeChecker_Env.lookup_lid env.tcenv lid)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7433))
in (match (uu____7428) with
| (uu____7464, t) -> begin
(

let uu____7466 = (

let uu____7467 = (normalize1 t)
in N (uu____7467))
in ((uu____7466), (e), (e)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____7468; FStar_Syntax_Syntax.vars = uu____7469}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____7548 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____7548) with
| (unary_op1, uu____7572) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____7643; FStar_Syntax_Syntax.vars = uu____7644}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____7740 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____7740) with
| (unary_op1, uu____7764) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____7843; FStar_Syntax_Syntax.vars = uu____7844}, ((a, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____7882 = (infer env a)
in (match (uu____7882) with
| (t, s, u) -> begin
(

let uu____7898 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____7898) with
| (head1, uu____7922) -> begin
(

let uu____7947 = (

let uu____7948 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in N (uu____7948))
in (

let uu____7949 = (

let uu____7950 = (

let uu____7951 = (

let uu____7968 = (

let uu____7979 = (FStar_Syntax_Syntax.as_arg s)
in (uu____7979)::[])
in ((head1), (uu____7968)))
in FStar_Syntax_Syntax.Tm_app (uu____7951))
in (mk1 uu____7950))
in (

let uu____8016 = (

let uu____8017 = (

let uu____8018 = (

let uu____8035 = (

let uu____8046 = (FStar_Syntax_Syntax.as_arg u)
in (uu____8046)::[])
in ((head1), (uu____8035)))
in FStar_Syntax_Syntax.Tm_app (uu____8018))
in (mk1 uu____8017))
in ((uu____7947), (uu____7949), (uu____8016)))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8083; FStar_Syntax_Syntax.vars = uu____8084}, ((a1, uu____8086))::(a2)::[]) -> begin
(

let uu____8142 = (infer env a1)
in (match (uu____8142) with
| (t, s, u) -> begin
(

let uu____8158 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____8158) with
| (head1, uu____8182) -> begin
(

let uu____8207 = (

let uu____8208 = (

let uu____8209 = (

let uu____8226 = (

let uu____8237 = (FStar_Syntax_Syntax.as_arg s)
in (uu____8237)::(a2)::[])
in ((head1), (uu____8226)))
in FStar_Syntax_Syntax.Tm_app (uu____8209))
in (mk1 uu____8208))
in (

let uu____8282 = (

let uu____8283 = (

let uu____8284 = (

let uu____8301 = (

let uu____8312 = (FStar_Syntax_Syntax.as_arg u)
in (uu____8312)::(a2)::[])
in ((head1), (uu____8301)))
in FStar_Syntax_Syntax.Tm_app (uu____8284))
in (mk1 uu____8283))
in ((t), (uu____8207), (uu____8282))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____8357; FStar_Syntax_Syntax.vars = uu____8358}, uu____8359) -> begin
(

let uu____8384 = (

let uu____8389 = (

let uu____8390 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8390))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____8389)))
in (FStar_Errors.raise_error uu____8384 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____8397; FStar_Syntax_Syntax.vars = uu____8398}, uu____8399) -> begin
(

let uu____8424 = (

let uu____8429 = (

let uu____8430 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8430))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____8429)))
in (FStar_Errors.raise_error uu____8424 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____8463 = (check_n env head1)
in (match (uu____8463) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____8485 = (

let uu____8486 = (FStar_Syntax_Subst.compress t)
in uu____8486.FStar_Syntax_Syntax.n)
in (match (uu____8485) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8489) -> begin
true
end
| uu____8504 -> begin
false
end)))
in (

let rec flatten1 = (fun t -> (

let uu____8525 = (

let uu____8526 = (FStar_Syntax_Subst.compress t)
in uu____8526.FStar_Syntax_Syntax.n)
in (match (uu____8525) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t1, uu____8545); FStar_Syntax_Syntax.pos = uu____8546; FStar_Syntax_Syntax.vars = uu____8547}) when (is_arrow t1) -> begin
(

let uu____8576 = (flatten1 t1)
in (match (uu____8576) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____8676, uu____8677) -> begin
(flatten1 e1)
end
| uu____8718 -> begin
(

let uu____8719 = (

let uu____8724 = (

let uu____8725 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" uu____8725))
in ((FStar_Errors.Fatal_NotFunctionType), (uu____8724)))
in (FStar_Errors.raise_err uu____8719))
end)))
in (

let uu____8740 = (flatten1 t_head)
in (match (uu____8740) with
| (binders, comp) -> begin
(

let n1 = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(

let uu____8814 = (

let uu____8819 = (

let uu____8820 = (FStar_Util.string_of_int n1)
in (

let uu____8827 = (FStar_Util.string_of_int (n' - n1))
in (

let uu____8838 = (FStar_Util.string_of_int n1)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." uu____8820 uu____8827 uu____8838))))
in ((FStar_Errors.Fatal_BinderAndArgsLengthMismatch), (uu____8819)))
in (FStar_Errors.raise_err uu____8814))
end
| uu____8845 -> begin
()
end);
(

let uu____8846 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____8846) with
| (binders1, comp1) -> begin
(

let rec final_type = (fun subst1 uu____8899 args1 -> (match (uu____8899) with
| (binders2, comp2) -> begin
(match (((binders2), (args1))) with
| ([], []) -> begin
(

let uu____8999 = (FStar_Syntax_Subst.subst_comp subst1 comp2)
in (nm_of_comp uu____8999))
end
| (binders3, []) -> begin
(

let uu____9037 = (

let uu____9038 = (

let uu____9041 = (

let uu____9042 = (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders3), (comp2)))))
in (FStar_Syntax_Subst.subst subst1 uu____9042))
in (FStar_Syntax_Subst.compress uu____9041))
in uu____9038.FStar_Syntax_Syntax.n)
in (match (uu____9037) with
| FStar_Syntax_Syntax.Tm_arrow (binders4, comp3) -> begin
(

let uu____9075 = (

let uu____9076 = (

let uu____9077 = (

let uu____9092 = (FStar_Syntax_Subst.close_comp binders4 comp3)
in ((binders4), (uu____9092)))
in FStar_Syntax_Syntax.Tm_arrow (uu____9077))
in (mk1 uu____9076))
in N (uu____9075))
end
| uu____9105 -> begin
(failwith "wat?")
end))
end
| ([], (uu____9106)::uu____9107) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____9159))::binders3, ((arg, uu____9162))::args2) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst1) ((binders3), (comp2)) args2)
end)
end))
in (

let final_type1 = (final_type [] ((binders1), (comp1)) args)
in (

let uu____9249 = (FStar_List.splitAt n' binders1)
in (match (uu____9249) with
| (binders2, uu____9287) -> begin
(

let uu____9320 = (

let uu____9343 = (FStar_List.map2 (fun uu____9405 uu____9406 -> (match (((uu____9405), (uu____9406))) with
| ((bv, uu____9454), (arg, q)) -> begin
(

let uu____9483 = (

let uu____9484 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in uu____9484.FStar_Syntax_Syntax.n)
in (match (uu____9483) with
| FStar_Syntax_Syntax.Tm_type (uu____9505) -> begin
(

let uu____9506 = (

let uu____9513 = (star_type' env arg)
in ((uu____9513), (q)))
in ((uu____9506), ((((arg), (q)))::[])))
end
| uu____9550 -> begin
(

let uu____9551 = (check_n env arg)
in (match (uu____9551) with
| (uu____9576, s_arg, u_arg) -> begin
(

let uu____9579 = (

let uu____9588 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____9588) with
| true -> begin
(

let uu____9597 = (

let uu____9604 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((uu____9604), (q)))
in (uu____9597)::(((u_arg), (q)))::[])
end
| uu____9627 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (uu____9579)))
end))
end))
end)) binders2 args)
in (FStar_List.split uu____9343))
in (match (uu____9320) with
| (s_args, u_args) -> begin
(

let u_args1 = (FStar_List.flatten u_args)
in (

let uu____9731 = (mk1 (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (

let uu____9744 = (mk1 (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args1)))))
in ((final_type1), (uu____9731), (uu____9744)))))
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
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____9810) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____9816) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____9822, uu____9823) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9865 = (

let uu____9866 = (env.tc_const c)
in N (uu____9866))
in ((uu____9865), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qt) -> begin
((N (FStar_Syntax_Syntax.t_term)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_let (uu____9873) -> begin
(

let uu____9886 = (

let uu____9887 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" uu____9887))
in (failwith uu____9886))
end
| FStar_Syntax_Syntax.Tm_type (uu____9894) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9901) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____9922) -> begin
(

let uu____9929 = (

let uu____9930 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" uu____9930))
in (failwith uu____9929))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9937) -> begin
(

let uu____9950 = (

let uu____9951 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" uu____9951))
in (failwith uu____9950))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____9958) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____9987 = (

let uu____9988 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" uu____9988))
in (failwith uu____9987))
end)))))
and mk_match : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e0.FStar_Syntax_Syntax.pos))
in (

let uu____10035 = (check_n env e0)
in (match (uu____10035) with
| (uu____10048, s_e0, u_e0) -> begin
(

let uu____10051 = (

let uu____10080 = (FStar_List.map (fun b -> (

let uu____10141 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____10141) with
| (pat, FStar_Pervasives_Native.None, body) -> begin
(

let env1 = (

let uu___378_10183 = env
in (

let uu____10184 = (

let uu____10185 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.tcenv uu____10185))
in {tcenv = uu____10184; subst = uu___378_10183.subst; tc_const = uu___378_10183.tc_const}))
in (

let uu____10188 = (f env1 body)
in (match (uu____10188) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (FStar_Pervasives_Native.None), (((s_body), (u_body), (body))))))
end)))
end
| uu____10260 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_WhenClauseNotSupported), ("No when clauses in the definition language")))
end))) branches)
in (FStar_List.split uu____10080))
in (match (uu____10051) with
| (nms, branches1) -> begin
(

let t1 = (

let uu____10364 = (FStar_List.hd nms)
in (match (uu____10364) with
| M (t1) -> begin
t1
end
| N (t1) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___361_10372 -> (match (uu___361_10372) with
| M (uu____10373) -> begin
true
end
| uu____10374 -> begin
false
end)) nms)
in (

let uu____10375 = (

let uu____10412 = (FStar_List.map2 (fun nm uu____10502 -> (match (uu____10502) with
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

let uu____10679 = (check env original_body (M (t2)))
in (match (uu____10679) with
| (uu____10716, s_body1, u_body1) -> begin
((M (t2)), (((pat), (guard), (s_body1))), (((pat), (guard), (u_body1))))
end))
end
| (M (uu____10755), false) -> begin
(failwith "impossible")
end)
end)) nms branches1)
in (FStar_List.unzip3 uu____10412))
in (match (uu____10375) with
| (nms1, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk1 env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_branches1 = (FStar_List.map (fun uu____10939 -> (match (uu____10939) with
| (pat, guard, s_body) -> begin
(

let s_body1 = (

let uu____10990 = (

let uu____10991 = (

let uu____11008 = (

let uu____11019 = (

let uu____11028 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____11031 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____11028), (uu____11031))))
in (uu____11019)::[])
in ((s_body), (uu____11008)))
in FStar_Syntax_Syntax.Tm_app (uu____10991))
in (mk1 uu____10990))
in ((pat), (guard), (s_body1)))
end)) s_branches)
in (

let s_branches2 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches1)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (

let uu____11165 = (

let uu____11166 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____11166)::[])
in (

let uu____11185 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches2)))))
in (FStar_Syntax_Util.abs uu____11165 uu____11185 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))
in (

let t1_star = (

let uu____11209 = (

let uu____11218 = (

let uu____11225 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____11225))
in (uu____11218)::[])
in (

let uu____11244 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____11209 uu____11244)))
in (

let uu____11247 = (mk1 (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))))
in (

let uu____11286 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((M (t1)), (uu____11247), (uu____11286)))))))))))
end
| uu____11305 -> begin
(

let s_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (

let uu____11395 = (

let uu____11396 = (

let uu____11397 = (

let uu____11424 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches1)))))
in ((uu____11424), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____11397))
in (mk1 uu____11396))
in (

let uu____11483 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((N (t1)), (uu____11395), (uu____11483)))))))
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

let uu____11548 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____11548)::[])
in (

let uu____11567 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____11567) with
| (x_binders1, e21) -> begin
(

let uu____11580 = (infer env e1)
in (match (uu____11580) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____11597 = (is_C t1)
in (match (uu____11597) with
| true -> begin
(

let uu___379_11598 = binding
in (

let uu____11599 = (

let uu____11602 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 uu____11602))
in {FStar_Syntax_Syntax.lbname = uu___379_11598.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___379_11598.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____11599; FStar_Syntax_Syntax.lbeff = uu___379_11598.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___379_11598.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___379_11598.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___379_11598.FStar_Syntax_Syntax.lbpos}))
end
| uu____11603 -> begin
binding
end))
in (

let env1 = (

let uu___380_11605 = env
in (

let uu____11606 = (FStar_TypeChecker_Env.push_bv env.tcenv (

let uu___381_11608 = x
in {FStar_Syntax_Syntax.ppname = uu___381_11608.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___381_11608.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {tcenv = uu____11606; subst = uu___380_11605.subst; tc_const = uu___380_11605.tc_const}))
in (

let uu____11609 = (proceed env1 e21)
in (match (uu____11609) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___382_11626 = binding
in (

let uu____11627 = (star_type' env1 binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___382_11626.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___382_11626.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____11627; FStar_Syntax_Syntax.lbeff = uu___382_11626.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___382_11626.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___382_11626.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___382_11626.FStar_Syntax_Syntax.lbpos}))
in (

let uu____11630 = (

let uu____11631 = (

let uu____11632 = (

let uu____11645 = (FStar_Syntax_Subst.close x_binders1 s_e2)
in ((((false), (((

let uu___383_11659 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___383_11659.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___383_11659.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___383_11659.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___383_11659.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1; FStar_Syntax_Syntax.lbattrs = uu___383_11659.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___383_11659.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____11645)))
in FStar_Syntax_Syntax.Tm_let (uu____11632))
in (mk1 uu____11631))
in (

let uu____11660 = (

let uu____11661 = (

let uu____11662 = (

let uu____11675 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___384_11689 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___384_11689.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___384_11689.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___384_11689.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___384_11689.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___384_11689.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___384_11689.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____11675)))
in FStar_Syntax_Syntax.Tm_let (uu____11662))
in (mk1 uu____11661))
in ((nm_rec), (uu____11630), (uu____11660)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___385_11694 = binding
in {FStar_Syntax_Syntax.lbname = uu___385_11694.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___385_11694.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___385_11694.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___385_11694.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___385_11694.FStar_Syntax_Syntax.lbpos})
in (

let env1 = (

let uu___386_11696 = env
in (

let uu____11697 = (FStar_TypeChecker_Env.push_bv env.tcenv (

let uu___387_11699 = x
in {FStar_Syntax_Syntax.ppname = uu___387_11699.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___387_11699.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {tcenv = uu____11697; subst = uu___386_11696.subst; tc_const = uu___386_11696.tc_const}))
in (

let uu____11700 = (ensure_m env1 e21)
in (match (uu____11700) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk1 env1 t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_e21 = (

let uu____11723 = (

let uu____11724 = (

let uu____11741 = (

let uu____11752 = (

let uu____11761 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____11764 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____11761), (uu____11764))))
in (uu____11752)::[])
in ((s_e2), (uu____11741)))
in FStar_Syntax_Syntax.Tm_app (uu____11724))
in (mk1 uu____11723))
in (

let s_e22 = (FStar_Syntax_Util.abs x_binders1 s_e21 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let body = (

let uu____11805 = (

let uu____11806 = (

let uu____11823 = (

let uu____11834 = (

let uu____11843 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e22), (uu____11843)))
in (uu____11834)::[])
in ((s_e1), (uu____11823)))
in FStar_Syntax_Syntax.Tm_app (uu____11806))
in (mk1 uu____11805))
in (

let uu____11878 = (

let uu____11879 = (

let uu____11880 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____11880)::[])
in (FStar_Syntax_Util.abs uu____11879 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
in (

let uu____11899 = (

let uu____11900 = (

let uu____11901 = (

let uu____11914 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___388_11928 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___388_11928.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___388_11928.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___388_11928.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___388_11928.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___388_11928.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___388_11928.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____11914)))
in FStar_Syntax_Syntax.Tm_let (uu____11901))
in (mk1 uu____11900))
in ((M (t2)), (uu____11878), (uu____11899)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____11938 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in N (uu____11938))
in (

let uu____11939 = (check env e mn)
in (match (uu____11939) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____11955 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____11977 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in M (uu____11977))
in (

let uu____11978 = (check env e mn)
in (match (uu____11978) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____11994 -> begin
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

let uu____12026 = (

let uu____12027 = (is_C c)
in (not (uu____12027)))
in (match (uu____12026) with
| true -> begin
(failwith "not a C")
end
| uu____12028 -> begin
()
end));
(

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (

let uu____12037 = (

let uu____12038 = (FStar_Syntax_Subst.compress c)
in uu____12038.FStar_Syntax_Syntax.n)
in (match (uu____12037) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____12067 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____12067) with
| (wp_head, wp_args) -> begin
((

let uu____12111 = ((not ((Prims.op_Equality (FStar_List.length wp_args) (FStar_List.length args)))) || (

let uu____12129 = (

let uu____12130 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head uu____12130))
in (not (uu____12129))))
in (match (uu____12111) with
| true -> begin
(failwith "mismatch")
end
| uu____12139 -> begin
()
end));
(

let uu____12140 = (

let uu____12141 = (

let uu____12158 = (FStar_List.map2 (fun uu____12196 uu____12197 -> (match (((uu____12196), (uu____12197))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q1 -> (

let uu____12258 = (FStar_Syntax_Syntax.is_implicit q1)
in (match (uu____12258) with
| true -> begin
"implicit"
end
| uu____12259 -> begin
"explicit"
end)))
in ((

let uu____12261 = (

let uu____12262 = (FStar_Syntax_Util.eq_aqual q q')
in (Prims.op_disEquality uu____12262 FStar_Syntax_Util.Equal))
in (match (uu____12261) with
| true -> begin
(

let uu____12263 = (

let uu____12268 = (

let uu____12269 = (print_implicit q)
in (

let uu____12270 = (print_implicit q')
in (FStar_Util.format2 "Incoherent implicit qualifiers %s %s\n" uu____12269 uu____12270)))
in ((FStar_Errors.Warning_IncoherentImplicitQualifier), (uu____12268)))
in (FStar_Errors.log_issue head1.FStar_Syntax_Syntax.pos uu____12263))
end
| uu____12271 -> begin
()
end));
(

let uu____12272 = (trans_F_ env arg wp_arg)
in ((uu____12272), (q)));
))
end)) args wp_args)
in ((head1), (uu____12158)))
in FStar_Syntax_Syntax.Tm_app (uu____12141))
in (mk1 uu____12140));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders1 = (FStar_Syntax_Util.name_binders binders)
in (

let uu____12318 = (FStar_Syntax_Subst.open_comp binders1 comp)
in (match (uu____12318) with
| (binders_orig, comp1) -> begin
(

let uu____12325 = (

let uu____12342 = (FStar_List.map (fun uu____12382 -> (match (uu____12382) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____12410 = (is_C h)
in (match (uu____12410) with
| true -> begin
(

let w' = (

let uu____12424 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w\'") FStar_Pervasives_Native.None uu____12424))
in (

let uu____12425 = (

let uu____12434 = (

let uu____12443 = (

let uu____12450 = (

let uu____12451 = (

let uu____12452 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h uu____12452))
in (FStar_Syntax_Syntax.null_bv uu____12451))
in ((uu____12450), (q)))
in (uu____12443)::[])
in (((w'), (q)))::uu____12434)
in ((w'), (uu____12425))))
end
| uu____12483 -> begin
(

let x = (

let uu____12485 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__x") FStar_Pervasives_Native.None uu____12485))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig)
in (FStar_List.split uu____12342))
in (match (uu____12325) with
| (bvs, binders2) -> begin
(

let binders3 = (FStar_List.flatten binders2)
in (

let comp2 = (

let uu____12558 = (

let uu____12561 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig uu____12561))
in (FStar_Syntax_Subst.subst_comp uu____12558 comp1))
in (

let app = (

let uu____12565 = (

let uu____12566 = (

let uu____12583 = (FStar_List.map (fun bv -> (

let uu____12602 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____12603 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____12602), (uu____12603))))) bvs)
in ((wp), (uu____12583)))
in FStar_Syntax_Syntax.Tm_app (uu____12566))
in (mk1 uu____12565))
in (

let comp3 = (

let uu____12617 = (type_of_comp comp2)
in (

let uu____12618 = (is_monadic_comp comp2)
in (trans_G env uu____12617 uu____12618 app)))
in (FStar_Syntax_Util.arrow binders3 comp3)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____12620, uu____12621) -> begin
(trans_F_ env e wp)
end
| uu____12662 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic1 wp -> (match (is_monadic1) with
| true -> begin
(

let uu____12667 = (

let uu____12668 = (star_type' env h)
in (

let uu____12671 = (

let uu____12682 = (

let uu____12691 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (uu____12691)))
in (uu____12682)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu____12668; FStar_Syntax_Syntax.effect_args = uu____12671; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____12667))
end
| uu____12714 -> begin
(

let uu____12715 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total uu____12715))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____12734 = (n env.tcenv t)
in (star_type' env uu____12734)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (

let uu____12753 = (n env.tcenv t)
in (check_n env uu____12753)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let uu____12769 = (n env.tcenv c)
in (

let uu____12770 = (n env.tcenv wp)
in (trans_F_ env uu____12769 uu____12770))))




