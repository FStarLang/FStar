
open Prims
open FStar_Pervasives
type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let __proj__Mkenv__item__env : env  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {env = __fname__env; subst = __fname__subst; tc_const = __fname__tc_const} -> begin
__fname__env
end))


let __proj__Mkenv__item__subst : env  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun projectee -> (match (projectee) with
| {env = __fname__env; subst = __fname__subst; tc_const = __fname__tc_const} -> begin
__fname__subst
end))


let __proj__Mkenv__item__tc_const : env  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {env = __fname__env; subst = __fname__subst; tc_const = __fname__tc_const} -> begin
__fname__tc_const
end))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a1 = (

let uu___79_123 = a
in (

let uu____124 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___79_123.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___79_123.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____124}))
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

let uu____150 = (

let uu____151 = (

let uu____154 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____154))
in uu____151.FStar_Syntax_Syntax.n)
in (match (uu____150) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t1, uu____183) -> begin
t1
end
| uu____192 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (

let uu____193 = (collect_binders rest)
in (FStar_List.append bs uu____193)))
end
| FStar_Syntax_Syntax.Tm_type (uu____204) -> begin
[]
end
| uu____209 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let gamma = (

let uu____229 = (collect_binders wp_a1)
in (FStar_All.pipe_right uu____229 FStar_Syntax_Util.name_binders))
in ((

let uu____249 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____249) with
| true -> begin
(

let uu____250 = (

let uu____251 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" uu____251))
in (d uu____250))
end
| uu____252 -> begin
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

let uu____285 = (FStar_TypeChecker_Util.mk_toplevel_definition env1 lident def)
in (match (uu____285) with
| (sigelt, fv) -> begin
((

let uu____293 = (

let uu____296 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____296)
in (FStar_ST.op_Colon_Equals sigelts uu____293));
fv;
)
end)))
in (

let binders_of_list1 = (FStar_List.map (fun uu____426 -> (match (uu____426) with
| (t, b) -> begin
(

let uu____437 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (uu____437)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (

let uu____470 = (FStar_Syntax_Syntax.as_implicit true)
in (((FStar_Pervasives_Native.fst t)), (uu____470)))))
in (

let args_of_binders1 = (FStar_List.map (fun bv -> (

let uu____495 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst bv))
in (FStar_Syntax_Syntax.as_arg uu____495))))
in (

let uu____496 = (

let uu____513 = (

let mk2 = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let body = (

let uu____537 = (

let uu____540 = (FStar_Syntax_Syntax.bv_to_name t)
in (f uu____540))
in (FStar_Syntax_Util.arrow gamma uu____537))
in (

let uu____541 = (

let uu____542 = (

let uu____549 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____554 = (

let uu____561 = (FStar_Syntax_Syntax.mk_binder t)
in (uu____561)::[])
in (uu____549)::uu____554))
in (FStar_List.append binders uu____542))
in (FStar_Syntax_Util.abs uu____541 body FStar_Pervasives_Native.None)))))
in (

let uu____582 = (mk2 FStar_Syntax_Syntax.mk_Total)
in (

let uu____583 = (mk2 FStar_Syntax_Syntax.mk_GTotal)
in ((uu____582), (uu____583)))))
in (match (uu____513) with
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

let uu____623 = (

let uu____624 = (

let uu____639 = (

let uu____648 = (FStar_List.map (fun uu____668 -> (match (uu____668) with
| (bv, uu____678) -> begin
(

let uu____679 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____680 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____679), (uu____680))))
end)) binders)
in (

let uu____681 = (

let uu____688 = (

let uu____693 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____694 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____693), (uu____694))))
in (

let uu____695 = (

let uu____702 = (

let uu____707 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (uu____707)))
in (uu____702)::[])
in (uu____688)::uu____695))
in (FStar_List.append uu____648 uu____681)))
in ((fv), (uu____639)))
in FStar_Syntax_Syntax.Tm_app (uu____624))
in (mk1 uu____623)))
in ((env), ((mk_app1 ctx_fv)), ((mk_app1 gctx_fv))))))))
end))
in (match (uu____496) with
| (env1, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let x = (

let uu____776 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None uu____776))
in (

let ret1 = (

let uu____780 = (

let uu____781 = (

let uu____784 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx uu____784))
in (FStar_Syntax_Util.residual_tot uu____781))
in FStar_Pervasives_Native.Some (uu____780))
in (

let body = (

let uu____788 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma uu____788 ret1))
in (

let uu____791 = (

let uu____792 = (mk_all_implicit binders)
in (

let uu____799 = (binders_of_list1 ((((a1), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append uu____792 uu____799)))
in (FStar_Syntax_Util.abs uu____791 body ret1))))))
in (

let c_pure1 = (

let uu____827 = (mk_lid "pure")
in (register env1 uu____827 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let l = (

let uu____834 = (

let uu____835 = (

let uu____836 = (

let uu____843 = (

let uu____848 = (

let uu____849 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____849))
in (FStar_Syntax_Syntax.mk_binder uu____848))
in (uu____843)::[])
in (

let uu____858 = (

let uu____861 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____861))
in (FStar_Syntax_Util.arrow uu____836 uu____858)))
in (mk_gctx uu____835))
in (FStar_Syntax_Syntax.gen_bv "l" FStar_Pervasives_Native.None uu____834))
in (

let r = (

let uu____863 = (

let uu____864 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____864))
in (FStar_Syntax_Syntax.gen_bv "r" FStar_Pervasives_Native.None uu____863))
in (

let ret1 = (

let uu____868 = (

let uu____869 = (

let uu____872 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____872))
in (FStar_Syntax_Util.residual_tot uu____869))
in FStar_Pervasives_Native.Some (uu____868))
in (

let outer_body = (

let gamma_as_args = (args_of_binders1 gamma)
in (

let inner_body = (

let uu____882 = (FStar_Syntax_Syntax.bv_to_name l)
in (

let uu____885 = (

let uu____894 = (

let uu____897 = (

let uu____898 = (

let uu____899 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app uu____899 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg uu____898))
in (uu____897)::[])
in (FStar_List.append gamma_as_args uu____894))
in (FStar_Syntax_Util.mk_app uu____882 uu____885)))
in (FStar_Syntax_Util.abs gamma inner_body ret1)))
in (

let uu____902 = (

let uu____903 = (mk_all_implicit binders)
in (

let uu____910 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append uu____903 uu____910)))
in (FStar_Syntax_Util.abs uu____902 outer_body ret1))))))))
in (

let c_app1 = (

let uu____946 = (mk_lid "app")
in (register env1 uu____946 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____955 = (

let uu____962 = (

let uu____967 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____967))
in (uu____962)::[])
in (

let uu____976 = (

let uu____979 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____979))
in (FStar_Syntax_Util.arrow uu____955 uu____976)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____982 = (

let uu____983 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____983))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____982))
in (

let ret1 = (

let uu____987 = (

let uu____988 = (

let uu____991 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____991))
in (FStar_Syntax_Util.residual_tot uu____988))
in FStar_Pervasives_Native.Some (uu____987))
in (

let uu____992 = (

let uu____993 = (mk_all_implicit binders)
in (

let uu____1000 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a11), (false)))::[]))
in (FStar_List.append uu____993 uu____1000)))
in (

let uu____1035 = (

let uu____1038 = (

let uu____1047 = (

let uu____1050 = (

let uu____1051 = (

let uu____1060 = (

let uu____1063 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1063)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1060))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1051))
in (

let uu____1070 = (

let uu____1073 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1073)::[])
in (uu____1050)::uu____1070))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1047))
in (FStar_Syntax_Util.mk_app c_app1 uu____1038))
in (FStar_Syntax_Util.abs uu____992 uu____1035 ret1)))))))))
in (

let c_lift11 = (

let uu____1081 = (mk_lid "lift1")
in (register env1 uu____1081 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1091 = (

let uu____1098 = (

let uu____1103 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1103))
in (

let uu____1104 = (

let uu____1111 = (

let uu____1116 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder uu____1116))
in (uu____1111)::[])
in (uu____1098)::uu____1104))
in (

let uu____1129 = (

let uu____1132 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal uu____1132))
in (FStar_Syntax_Util.arrow uu____1091 uu____1129)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let a11 = (

let uu____1135 = (

let uu____1136 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____1136))
in (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None uu____1135))
in (

let a2 = (

let uu____1138 = (

let uu____1139 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1139))
in (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None uu____1138))
in (

let ret1 = (

let uu____1143 = (

let uu____1144 = (

let uu____1147 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx uu____1147))
in (FStar_Syntax_Util.residual_tot uu____1144))
in FStar_Pervasives_Native.Some (uu____1143))
in (

let uu____1148 = (

let uu____1149 = (mk_all_implicit binders)
in (

let uu____1156 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a11), (false)))::(((a2), (false)))::[]))
in (FStar_List.append uu____1149 uu____1156)))
in (

let uu____1199 = (

let uu____1202 = (

let uu____1211 = (

let uu____1214 = (

let uu____1215 = (

let uu____1224 = (

let uu____1227 = (

let uu____1228 = (

let uu____1237 = (

let uu____1240 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1240)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1237))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1228))
in (

let uu____1247 = (

let uu____1250 = (FStar_Syntax_Syntax.bv_to_name a11)
in (uu____1250)::[])
in (uu____1227)::uu____1247))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1224))
in (FStar_Syntax_Util.mk_app c_app1 uu____1215))
in (

let uu____1257 = (

let uu____1260 = (FStar_Syntax_Syntax.bv_to_name a2)
in (uu____1260)::[])
in (uu____1214)::uu____1257))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1211))
in (FStar_Syntax_Util.mk_app c_app1 uu____1202))
in (FStar_Syntax_Util.abs uu____1148 uu____1199 ret1)))))))))))
in (

let c_lift21 = (

let uu____1268 = (mk_lid "lift2")
in (register env1 uu____1268 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1277 = (

let uu____1284 = (

let uu____1289 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1289))
in (uu____1284)::[])
in (

let uu____1298 = (

let uu____1301 = (

let uu____1302 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____1302))
in (FStar_Syntax_Syntax.mk_Total uu____1301))
in (FStar_Syntax_Util.arrow uu____1277 uu____1298)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let ret1 = (

let uu____1307 = (

let uu____1308 = (

let uu____1311 = (

let uu____1312 = (

let uu____1319 = (

let uu____1324 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____1324))
in (uu____1319)::[])
in (

let uu____1333 = (

let uu____1336 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____1336))
in (FStar_Syntax_Util.arrow uu____1312 uu____1333)))
in (mk_ctx uu____1311))
in (FStar_Syntax_Util.residual_tot uu____1308))
in FStar_Pervasives_Native.Some (uu____1307))
in (

let e1 = (

let uu____1338 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" FStar_Pervasives_Native.None uu____1338))
in (

let body = (

let uu____1342 = (

let uu____1343 = (

let uu____1350 = (FStar_Syntax_Syntax.mk_binder e1)
in (uu____1350)::[])
in (FStar_List.append gamma uu____1343))
in (

let uu____1367 = (

let uu____1370 = (FStar_Syntax_Syntax.bv_to_name f)
in (

let uu____1373 = (

let uu____1382 = (

let uu____1383 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg uu____1383))
in (

let uu____1384 = (args_of_binders1 gamma)
in (uu____1382)::uu____1384))
in (FStar_Syntax_Util.mk_app uu____1370 uu____1373)))
in (FStar_Syntax_Util.abs uu____1342 uu____1367 ret1)))
in (

let uu____1387 = (

let uu____1388 = (mk_all_implicit binders)
in (

let uu____1395 = (binders_of_list1 ((((a1), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append uu____1388 uu____1395)))
in (FStar_Syntax_Util.abs uu____1387 body ret1)))))))))
in (

let c_push1 = (

let uu____1427 = (mk_lid "push")
in (register env1 uu____1427 c_push))
in (

let ret_tot_wp_a = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot wp_a1))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1449 = (

let uu____1450 = (

let uu____1465 = (args_of_binders1 binders)
in ((c), (uu____1465)))
in FStar_Syntax_Syntax.Tm_app (uu____1450))
in (mk1 uu____1449))
end
| uu____1484 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (

let uu____1489 = (

let uu____1490 = (

let uu____1497 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (

let uu____1502 = (

let uu____1509 = (FStar_Syntax_Syntax.null_binder wp_a1)
in (uu____1509)::[])
in (uu____1497)::uu____1502))
in (

let uu____1526 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____1490 uu____1526)))
in (FStar_Syntax_Syntax.mk_Total uu____1489))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let uu____1530 = (

let uu____1531 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(c)::[]))
in (FStar_List.append binders uu____1531))
in (

let uu____1542 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____1546 = (

let uu____1549 = (

let uu____1558 = (

let uu____1561 = (

let uu____1562 = (

let uu____1571 = (

let uu____1578 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg uu____1578))
in (uu____1571)::[])
in (FStar_Syntax_Util.mk_app l_ite uu____1562))
in (uu____1561)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1558))
in (FStar_Syntax_Util.mk_app c_lift21 uu____1549))
in (FStar_Syntax_Util.ascribe uu____1546 ((FStar_Util.Inr (result_comp)), (FStar_Pervasives_Native.None)))))
in (FStar_Syntax_Util.abs uu____1530 uu____1542 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp result_comp))))))))
in (

let wp_if_then_else1 = (

let uu____1614 = (mk_lid "wp_if_then_else")
in (register env1 uu____1614 wp_if_then_else))
in (

let wp_if_then_else2 = (mk_generic_app wp_if_then_else1)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let body = (

let uu____1627 = (

let uu____1636 = (

let uu____1639 = (

let uu____1640 = (

let uu____1649 = (

let uu____1652 = (

let uu____1653 = (

let uu____1662 = (

let uu____1669 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1669))
in (uu____1662)::[])
in (FStar_Syntax_Util.mk_app l_and uu____1653))
in (uu____1652)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1649))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1640))
in (

let uu____1688 = (

let uu____1691 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1691)::[])
in (uu____1639)::uu____1688))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1636))
in (FStar_Syntax_Util.mk_app c_app1 uu____1627))
in (

let uu____1698 = (

let uu____1699 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1699))
in (FStar_Syntax_Util.abs uu____1698 body ret_tot_wp_a))))))
in (

let wp_assert1 = (

let uu____1711 = (mk_lid "wp_assert")
in (register env1 uu____1711 wp_assert))
in (

let wp_assert2 = (mk_generic_app wp_assert1)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let body = (

let uu____1724 = (

let uu____1733 = (

let uu____1736 = (

let uu____1737 = (

let uu____1746 = (

let uu____1749 = (

let uu____1750 = (

let uu____1759 = (

let uu____1766 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1766))
in (uu____1759)::[])
in (FStar_Syntax_Util.mk_app l_imp uu____1750))
in (uu____1749)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1746))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1737))
in (

let uu____1785 = (

let uu____1788 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1788)::[])
in (uu____1736)::uu____1785))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1733))
in (FStar_Syntax_Util.mk_app c_app1 uu____1724))
in (

let uu____1795 = (

let uu____1796 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1796))
in (FStar_Syntax_Util.abs uu____1795 body ret_tot_wp_a))))))
in (

let wp_assume1 = (

let uu____1808 = (mk_lid "wp_assume")
in (register env1 uu____1808 wp_assume))
in (

let wp_assume2 = (mk_generic_app wp_assume1)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" FStar_Pervasives_Native.None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1819 = (

let uu____1826 = (

let uu____1831 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1831))
in (uu____1826)::[])
in (

let uu____1840 = (FStar_Syntax_Syntax.mk_Total wp_a1)
in (FStar_Syntax_Util.arrow uu____1819 uu____1840)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" FStar_Pervasives_Native.None t_f)
in (

let body = (

let uu____1847 = (

let uu____1856 = (

let uu____1859 = (

let uu____1860 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure1 uu____1860))
in (

let uu____1875 = (

let uu____1878 = (

let uu____1879 = (

let uu____1888 = (

let uu____1891 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1891)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1888))
in (FStar_Syntax_Util.mk_app c_push1 uu____1879))
in (uu____1878)::[])
in (uu____1859)::uu____1875))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1856))
in (FStar_Syntax_Util.mk_app c_app1 uu____1847))
in (

let uu____1904 = (

let uu____1905 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(b)::(f)::[]))
in (FStar_List.append binders uu____1905))
in (FStar_Syntax_Util.abs uu____1904 body ret_tot_wp_a))))))
in (

let wp_close1 = (

let uu____1917 = (mk_lid "wp_close")
in (register env1 uu____1917 wp_close))
in (

let wp_close2 = (mk_generic_app wp_close1)
in (

let ret_tot_type = FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype))
in (

let ret_gtot_type = (

let uu____1927 = (

let uu____1928 = (

let uu____1929 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____1929))
in (FStar_Syntax_Util.residual_comp_of_lcomp uu____1928))
in FStar_Pervasives_Native.Some (uu____1927))
in (

let mk_forall1 = (fun x body -> (

let uu____1941 = (

let uu____1948 = (

let uu____1949 = (

let uu____1964 = (

let uu____1973 = (

let uu____1980 = (

let uu____1981 = (

let uu____1982 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1982)::[])
in (FStar_Syntax_Util.abs uu____1981 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg uu____1980))
in (uu____1973)::[])
in ((FStar_Syntax_Util.tforall), (uu____1964)))
in FStar_Syntax_Syntax.Tm_app (uu____1949))
in (FStar_Syntax_Syntax.mk uu____1948))
in (uu____1941 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (

let uu____2030 = (

let uu____2031 = (FStar_Syntax_Subst.compress t)
in uu____2031.FStar_Syntax_Syntax.n)
in (match (uu____2030) with
| FStar_Syntax_Syntax.Tm_type (uu____2034) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2060 -> (match (uu____2060) with
| (b, uu____2066) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____2067 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____2074 = (

let uu____2075 = (FStar_Syntax_Subst.compress t)
in uu____2075.FStar_Syntax_Syntax.n)
in (match (uu____2074) with
| FStar_Syntax_Syntax.Tm_type (uu____2078) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____2104 -> (match (uu____2104) with
| (b, uu____2110) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____2111 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel1 = (mk_rel rel)
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 t)
in (

let uu____2185 = (

let uu____2186 = (FStar_Syntax_Subst.compress t1)
in uu____2186.FStar_Syntax_Syntax.n)
in (match (uu____2185) with
| FStar_Syntax_Syntax.Tm_type (uu____2191) -> begin
(rel x y)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____2194); FStar_Syntax_Syntax.pos = uu____2195; FStar_Syntax_Syntax.vars = uu____2196}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2230 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2230) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2237 = (

let uu____2240 = (

let uu____2249 = (

let uu____2256 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2256))
in (uu____2249)::[])
in (FStar_Syntax_Util.mk_app x uu____2240))
in (

let uu____2269 = (

let uu____2272 = (

let uu____2281 = (

let uu____2288 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2288))
in (uu____2281)::[])
in (FStar_Syntax_Util.mk_app y uu____2272))
in (mk_rel1 b uu____2237 uu____2269)))
in (mk_forall1 a11 body)))
end
| uu____2301 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2305 = (

let uu____2308 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2311 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2308 uu____2311)))
in (

let uu____2314 = (

let uu____2315 = (

let uu____2318 = (

let uu____2327 = (

let uu____2334 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2334))
in (uu____2327)::[])
in (FStar_Syntax_Util.mk_app x uu____2318))
in (

let uu____2347 = (

let uu____2350 = (

let uu____2359 = (

let uu____2366 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____2366))
in (uu____2359)::[])
in (FStar_Syntax_Util.mk_app y uu____2350))
in (mk_rel1 b uu____2315 uu____2347)))
in (FStar_Syntax_Util.mk_imp uu____2305 uu____2314)))
in (

let uu____2379 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____2379)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____2382); FStar_Syntax_Syntax.pos = uu____2383; FStar_Syntax_Syntax.vars = uu____2384}) -> begin
(

let a2 = (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____2418 = ((is_monotonic a2) || (is_monotonic b))
in (match (uu____2418) with
| true -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2425 = (

let uu____2428 = (

let uu____2437 = (

let uu____2444 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2444))
in (uu____2437)::[])
in (FStar_Syntax_Util.mk_app x uu____2428))
in (

let uu____2457 = (

let uu____2460 = (

let uu____2469 = (

let uu____2476 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2476))
in (uu____2469)::[])
in (FStar_Syntax_Util.mk_app y uu____2460))
in (mk_rel1 b uu____2425 uu____2457)))
in (mk_forall1 a11 body)))
end
| uu____2489 -> begin
(

let a11 = (FStar_Syntax_Syntax.gen_bv "a1" FStar_Pervasives_Native.None a2)
in (

let a21 = (FStar_Syntax_Syntax.gen_bv "a2" FStar_Pervasives_Native.None a2)
in (

let body = (

let uu____2493 = (

let uu____2496 = (FStar_Syntax_Syntax.bv_to_name a11)
in (

let uu____2499 = (FStar_Syntax_Syntax.bv_to_name a21)
in (mk_rel1 a2 uu____2496 uu____2499)))
in (

let uu____2502 = (

let uu____2503 = (

let uu____2506 = (

let uu____2515 = (

let uu____2522 = (FStar_Syntax_Syntax.bv_to_name a11)
in (FStar_Syntax_Syntax.as_arg uu____2522))
in (uu____2515)::[])
in (FStar_Syntax_Util.mk_app x uu____2506))
in (

let uu____2535 = (

let uu____2538 = (

let uu____2547 = (

let uu____2554 = (FStar_Syntax_Syntax.bv_to_name a21)
in (FStar_Syntax_Syntax.as_arg uu____2554))
in (uu____2547)::[])
in (FStar_Syntax_Util.mk_app y uu____2538))
in (mk_rel1 b uu____2503 uu____2535)))
in (FStar_Syntax_Util.mk_imp uu____2493 uu____2502)))
in (

let uu____2567 = (mk_forall1 a21 body)
in (mk_forall1 a11 uu____2567)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders1, comp) -> begin
(

let t2 = (

let uu___80_2598 = t1
in (

let uu____2599 = (

let uu____2600 = (

let uu____2613 = (

let uu____2616 = (FStar_Syntax_Util.arrow binders1 comp)
in (FStar_Syntax_Syntax.mk_Total uu____2616))
in (((binder)::[]), (uu____2613)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2600))
in {FStar_Syntax_Syntax.n = uu____2599; FStar_Syntax_Syntax.pos = uu___80_2598.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___80_2598.FStar_Syntax_Syntax.vars}))
in (mk_rel1 t2 x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2633) -> begin
(failwith "unhandled arrow")
end
| uu____2648 -> begin
(FStar_Syntax_Util.mk_untyped_eq2 x y)
end)))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" FStar_Pervasives_Native.None wp_a1)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" FStar_Pervasives_Native.None wp_a1)
in (

let rec mk_stronger = (fun t x y -> (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 t)
in (

let uu____2685 = (

let uu____2686 = (FStar_Syntax_Subst.compress t1)
in uu____2686.FStar_Syntax_Syntax.n)
in (match (uu____2685) with
| FStar_Syntax_Syntax.Tm_type (uu____2691) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when (

let uu____2714 = (FStar_Syntax_Subst.compress head1)
in (FStar_Syntax_Util.is_tuple_constructor uu____2714)) -> begin
(

let project = (fun i tuple -> (

let projector = (

let uu____2733 = (

let uu____2734 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env1 uu____2734 i))
in (FStar_Syntax_Syntax.fvar uu____2733 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (FStar_Pervasives_Native.None)))::[]))))
in (

let uu____2757 = (

let uu____2766 = (FStar_List.mapi (fun i uu____2786 -> (match (uu____2786) with
| (t2, q) -> begin
(

let uu____2801 = (project i x)
in (

let uu____2804 = (project i y)
in (mk_stronger t2 uu____2801 uu____2804)))
end)) args)
in (match (uu____2766) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____2757) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, uu____2857); FStar_Syntax_Syntax.pos = uu____2858; FStar_Syntax_Syntax.vars = uu____2859}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____2897 -> (match (uu____2897) with
| (bv, q) -> begin
(

let uu____2904 = (

let uu____2905 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____2905))
in (FStar_Syntax_Syntax.gen_bv uu____2904 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____2912 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____2912))) bvs)
in (

let body = (

let uu____2916 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____2919 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____2916 uu____2919)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| FStar_Syntax_Syntax.Tm_arrow (binders1, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, uu____2928); FStar_Syntax_Syntax.pos = uu____2929; FStar_Syntax_Syntax.vars = uu____2930}) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____2968 -> (match (uu____2968) with
| (bv, q) -> begin
(

let uu____2975 = (

let uu____2976 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____2976))
in (FStar_Syntax_Syntax.gen_bv uu____2975 FStar_Pervasives_Native.None bv.FStar_Syntax_Syntax.sort))
end)) binders1)
in (

let args = (FStar_List.map (fun ai -> (

let uu____2983 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____2983))) bvs)
in (

let body = (

let uu____2987 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____2990 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____2987 uu____2990)))
in (FStar_List.fold_right (fun bv body1 -> (mk_forall1 bv body1)) bvs body))))
end
| uu____2997 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (

let uu____3003 = (FStar_Syntax_Util.unascribe wp_a1)
in (

let uu____3006 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (

let uu____3009 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger uu____3003 uu____3006 uu____3009))))
in (

let uu____3012 = (

let uu____3013 = (binders_of_list1 ((((a1), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders uu____3013))
in (FStar_Syntax_Util.abs uu____3012 body ret_tot_type))))))
in (

let stronger1 = (

let uu____3041 = (mk_lid "stronger")
in (register env1 uu____3041 stronger))
in (

let stronger2 = (mk_generic_app stronger1)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3049 = (FStar_Util.prefix gamma)
in (match (uu____3049) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv1 = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq1 = (

let uu____3098 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm uu____3098))
in (

let uu____3101 = (FStar_Syntax_Util.destruct_typ_as_formula eq1)
in (match (uu____3101) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (binders1, [], body)) -> begin
(

let k_app = (

let uu____3109 = (args_of_binders1 binders1)
in (FStar_Syntax_Util.mk_app k_tm uu____3109))
in (

let guard_free1 = (

let uu____3119 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.guard_free FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3119))
in (

let pat = (

let uu____3123 = (

let uu____3132 = (FStar_Syntax_Syntax.as_arg k_app)
in (uu____3132)::[])
in (FStar_Syntax_Util.mk_app guard_free1 uu____3123))
in (

let pattern_guarded_body = (

let uu____3154 = (

let uu____3155 = (

let uu____3162 = (

let uu____3163 = (

let uu____3174 = (

let uu____3183 = (FStar_Syntax_Syntax.as_arg pat)
in (uu____3183)::[])
in (uu____3174)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____3163))
in ((body), (uu____3162)))
in FStar_Syntax_Syntax.Tm_meta (uu____3155))
in (mk1 uu____3154))
in (FStar_Syntax_Util.close_forall_no_univs binders1 pattern_guarded_body)))))
end
| uu____3202 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (

let uu____3208 = (

let uu____3211 = (

let uu____3212 = (

let uu____3213 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____3216 = (

let uu____3225 = (args_of_binders1 wp_args)
in (

let uu____3228 = (

let uu____3231 = (

let uu____3232 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg uu____3232))
in (uu____3231)::[])
in (FStar_List.append uu____3225 uu____3228)))
in (FStar_Syntax_Util.mk_app uu____3213 uu____3216)))
in (FStar_Syntax_Util.mk_imp equiv1 uu____3212))
in (FStar_Syntax_Util.mk_forall_no_univ k uu____3211))
in (FStar_Syntax_Util.abs gamma uu____3208 ret_gtot_type))
in (

let uu____3233 = (

let uu____3234 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____3234))
in (FStar_Syntax_Util.abs uu____3233 body ret_gtot_type)))))
end)))
in (

let wp_ite1 = (

let uu____3246 = (mk_lid "wp_ite")
in (register env1 uu____3246 wp_ite))
in (

let wp_ite2 = (mk_generic_app wp_ite1)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let uu____3254 = (FStar_Util.prefix gamma)
in (match (uu____3254) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let body = (

let uu____3299 = (

let uu____3300 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst post))
in (

let uu____3305 = (

let uu____3314 = (

let uu____3321 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____3321))
in (uu____3314)::[])
in (FStar_Syntax_Util.mk_app uu____3300 uu____3305)))
in (FStar_Syntax_Util.mk_forall_no_univ x uu____3299))
in (

let uu____3334 = (

let uu____3335 = (

let uu____3342 = (FStar_Syntax_Syntax.binders_of_list ((a1)::[]))
in (FStar_List.append uu____3342 gamma))
in (FStar_List.append binders uu____3335))
in (FStar_Syntax_Util.abs uu____3334 body ret_gtot_type))))
end)))
in (

let null_wp1 = (

let uu____3358 = (mk_lid "null_wp")
in (register env1 uu____3358 null_wp))
in (

let null_wp2 = (mk_generic_app null_wp1)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None wp_a1)
in (

let body = (

let uu____3369 = (

let uu____3378 = (

let uu____3381 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3382 = (

let uu____3385 = (

let uu____3386 = (

let uu____3395 = (

let uu____3402 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____3402))
in (uu____3395)::[])
in (FStar_Syntax_Util.mk_app null_wp2 uu____3386))
in (

let uu____3415 = (

let uu____3418 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____3418)::[])
in (uu____3385)::uu____3415))
in (uu____3381)::uu____3382))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____3378))
in (FStar_Syntax_Util.mk_app stronger2 uu____3369))
in (

let uu____3425 = (

let uu____3426 = (FStar_Syntax_Syntax.binders_of_list ((a1)::(wp)::[]))
in (FStar_List.append binders uu____3426))
in (FStar_Syntax_Util.abs uu____3425 body ret_tot_type))))
in (

let wp_trivial1 = (

let uu____3438 = (mk_lid "wp_trivial")
in (register env1 uu____3438 wp_trivial))
in (

let wp_trivial2 = (mk_generic_app wp_trivial1)
in ((

let uu____3443 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3443) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____3444 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (

let uu____3450 = (

let uu____3451 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____3451))
in (

let uu____3503 = (

let uu___81_3504 = ed
in (

let uu____3505 = (

let uu____3506 = (c wp_if_then_else2)
in (([]), (uu____3506)))
in (

let uu____3513 = (

let uu____3514 = (c wp_ite2)
in (([]), (uu____3514)))
in (

let uu____3521 = (

let uu____3522 = (c stronger2)
in (([]), (uu____3522)))
in (

let uu____3529 = (

let uu____3530 = (c wp_close2)
in (([]), (uu____3530)))
in (

let uu____3537 = (

let uu____3538 = (c wp_assert2)
in (([]), (uu____3538)))
in (

let uu____3545 = (

let uu____3546 = (c wp_assume2)
in (([]), (uu____3546)))
in (

let uu____3553 = (

let uu____3554 = (c null_wp2)
in (([]), (uu____3554)))
in (

let uu____3561 = (

let uu____3562 = (c wp_trivial2)
in (([]), (uu____3562)))
in {FStar_Syntax_Syntax.cattributes = uu___81_3504.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___81_3504.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___81_3504.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___81_3504.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___81_3504.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___81_3504.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___81_3504.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu____3505; FStar_Syntax_Syntax.ite_wp = uu____3513; FStar_Syntax_Syntax.stronger = uu____3521; FStar_Syntax_Syntax.close_wp = uu____3529; FStar_Syntax_Syntax.assert_p = uu____3537; FStar_Syntax_Syntax.assume_p = uu____3545; FStar_Syntax_Syntax.null_wp = uu____3553; FStar_Syntax_Syntax.trivial = uu____3561; FStar_Syntax_Syntax.repr = uu___81_3504.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___81_3504.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___81_3504.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___81_3504.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___81_3504.FStar_Syntax_Syntax.eff_attrs})))))))))
in ((uu____3450), (uu____3503)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)


let set_env : env  ->  FStar_TypeChecker_Env.env  ->  env = (fun dmff_env env' -> (

let uu___82_3584 = dmff_env
in {env = env'; subst = uu___82_3584.subst; tc_const = uu___82_3584.tc_const}))

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____3601 -> begin
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
| uu____3615 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun uu___68_3627 -> (match (uu___68_3627) with
| FStar_Syntax_Syntax.Total (t, uu____3629) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___67_3642 -> (match (uu___67_3642) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____3643 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let uu____3645 = (

let uu____3646 = (

let uu____3647 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3647))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3646))
in (failwith uu____3645))
end
| FStar_Syntax_Syntax.GTotal (uu____3648) -> begin
(failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___69_3661 -> (match (uu___69_3661) with
| N (t) -> begin
(

let uu____3663 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" uu____3663))
end
| M (t) -> begin
(

let uu____3665 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" uu____3665))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n1 -> (match (n1) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3671, {FStar_Syntax_Syntax.n = n2; FStar_Syntax_Syntax.pos = uu____3673; FStar_Syntax_Syntax.vars = uu____3674}) -> begin
(nm_of_comp n2)
end
| uu____3691 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (

let uu____3701 = (nm_of_comp c.FStar_Syntax_Syntax.n)
in (match (uu____3701) with
| M (uu____3702) -> begin
true
end
| N (uu____3703) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____3709 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ1 -> (

let uu____3723 = (

let uu____3730 = (

let uu____3735 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3735))
in (uu____3730)::[])
in (

let uu____3748 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____3723 uu____3748))))
in (

let uu____3751 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once uu____3751))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun mk1 env a -> (

let uu____3792 = (

let uu____3793 = (

let uu____3806 = (

let uu____3813 = (

let uu____3818 = (

let uu____3819 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv uu____3819))
in (

let uu____3820 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3818), (uu____3820))))
in (uu____3813)::[])
in (

let uu____3829 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____3806), (uu____3829))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3793))
in (mk1 uu____3792)))
and star_type' : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type1 = (mk_star_to_type mk1)
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3867) -> begin
(

let binders1 = (FStar_List.map (fun uu____3903 -> (match (uu____3903) with
| (bv, aqual) -> begin
(

let uu____3914 = (

let uu___83_3915 = bv
in (

let uu____3916 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___83_3915.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___83_3915.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3916}))
in ((uu____3914), (aqual)))
end)) binders)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3919, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____3921); FStar_Syntax_Syntax.pos = uu____3922; FStar_Syntax_Syntax.vars = uu____3923}) -> begin
(

let uu____3948 = (

let uu____3949 = (

let uu____3962 = (

let uu____3965 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal uu____3965))
in ((binders1), (uu____3962)))
in FStar_Syntax_Syntax.Tm_arrow (uu____3949))
in (mk1 uu____3948))
end
| uu____3974 -> begin
(

let uu____3975 = (is_monadic_arrow t1.FStar_Syntax_Syntax.n)
in (match (uu____3975) with
| N (hn) -> begin
(

let uu____3977 = (

let uu____3978 = (

let uu____3991 = (

let uu____3994 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total uu____3994))
in ((binders1), (uu____3991)))
in FStar_Syntax_Syntax.Tm_arrow (uu____3978))
in (mk1 uu____3977))
end
| M (a) -> begin
(

let uu____4004 = (

let uu____4005 = (

let uu____4018 = (

let uu____4025 = (

let uu____4032 = (

let uu____4037 = (

let uu____4038 = (mk_star_to_type1 env a)
in (FStar_Syntax_Syntax.null_bv uu____4038))
in (

let uu____4039 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4037), (uu____4039))))
in (uu____4032)::[])
in (FStar_List.append binders1 uu____4025))
in (

let uu____4052 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____4018), (uu____4052))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4005))
in (mk1 uu____4004))
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

let uu____4134 = (f x)
in (FStar_Util.string_builder_append strb uu____4134));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____4141 = (f x1)
in (FStar_Util.string_builder_append strb uu____4141));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (

let uu____4143 = (

let uu____4148 = (

let uu____4149 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____4150 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.format2 "Dependency found in term %s : %s" uu____4149 uu____4150)))
in ((FStar_Errors.Warning_DependencyFound), (uu____4148)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4143))))
in (

let rec is_non_dependent_arrow = (fun ty n1 -> (

let uu____4166 = (

let uu____4167 = (FStar_Syntax_Subst.compress ty)
in uu____4167.FStar_Syntax_Syntax.n)
in (match (uu____4166) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____4188 = (

let uu____4189 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (not (uu____4189)))
in (match (uu____4188) with
| true -> begin
false
end
| uu____4190 -> begin
(FStar_All.try_with (fun uu___85_4200 -> (match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty1 -> (

let sinter = (

let uu____4219 = (FStar_Syntax_Free.names ty1)
in (FStar_Util.set_intersect uu____4219 s))
in (

let uu____4222 = (

let uu____4223 = (FStar_Util.set_is_empty sinter)
in (not (uu____4223)))
in (match (uu____4222) with
| true -> begin
((debug1 ty1 sinter);
(FStar_Exn.raise Not_found);
)
end
| uu____4225 -> begin
()
end))))
in (

let uu____4226 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____4226) with
| (binders1, c1) -> begin
(

let s = (FStar_List.fold_left (fun s uu____4248 -> (match (uu____4248) with
| (bv, uu____4258) -> begin
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
| uu____4269 -> begin
true
end));
)))
end)))
end)) (fun uu___84_4271 -> (match (uu___84_4271) with
| Not_found -> begin
false
end)))
end))
end
| uu____4272 -> begin
((

let uu____4274 = (

let uu____4279 = (

let uu____4280 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.format1 "Not a dependent arrow : %s" uu____4280))
in ((FStar_Errors.Warning_NotDependentArrow), (uu____4279)))
in (FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos uu____4274));
false;
)
end)))
in (

let rec is_valid_application = (fun head2 -> (

let uu____4287 = (

let uu____4288 = (FStar_Syntax_Subst.compress head2)
in uu____4288.FStar_Syntax_Syntax.n)
in (match (uu____4287) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (

let uu____4293 = (FStar_Syntax_Subst.compress head2)
in (FStar_Syntax_Util.is_tuple_constructor uu____4293))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4295 = (FStar_TypeChecker_Env.lookup_lid env.env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4295) with
| ((uu____4304, ty), uu____4306) -> begin
(

let uu____4311 = (is_non_dependent_arrow ty (FStar_List.length args))
in (match (uu____4311) with
| true -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t1)
in (

let uu____4319 = (

let uu____4320 = (FStar_Syntax_Subst.compress res)
in uu____4320.FStar_Syntax_Syntax.n)
in (match (uu____4319) with
| FStar_Syntax_Syntax.Tm_app (uu____4323) -> begin
true
end
| uu____4338 -> begin
((

let uu____4340 = (

let uu____4345 = (

let uu____4346 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.format1 "Got a term which might be a non-dependent user-defined data-type %s\n" uu____4346))
in ((FStar_Errors.Warning_NondependentUserDefinedDataType), (uu____4345)))
in (FStar_Errors.log_issue head2.FStar_Syntax_Syntax.pos uu____4340));
false;
)
end)))
end
| uu____4347 -> begin
false
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____4348) -> begin
true
end
| FStar_Syntax_Syntax.Tm_name (uu____4349) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____4351) -> begin
(is_valid_application t2)
end
| uu____4356 -> begin
false
end)))
in (

let uu____4357 = (is_valid_application head1)
in (match (uu____4357) with
| true -> begin
(

let uu____4358 = (

let uu____4359 = (

let uu____4374 = (FStar_List.map (fun uu____4397 -> (match (uu____4397) with
| (t2, qual) -> begin
(

let uu____4414 = (star_type' env t2)
in ((uu____4414), (qual)))
end)) args)
in ((head1), (uu____4374)))
in FStar_Syntax_Syntax.Tm_app (uu____4359))
in (mk1 uu____4358))
end
| uu____4425 -> begin
(

let uu____4426 = (

let uu____4431 = (

let uu____4432 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" uu____4432))
in ((FStar_Errors.Fatal_WrongTerm), (uu____4431)))
in (FStar_Errors.raise_err uu____4426))
end)))))
end
| FStar_Syntax_Syntax.Tm_bvar (uu____4433) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____4434) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____4435) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4436) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____4460 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____4460) with
| (binders1, repr1) -> begin
(

let env1 = (

let uu___86_4468 = env
in (

let uu____4469 = (FStar_TypeChecker_Env.push_binders env.env binders1)
in {env = uu____4469; subst = uu___86_4468.subst; tc_const = uu___86_4468.tc_const}))
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

let uu___87_4491 = x1
in {FStar_Syntax_Syntax.ppname = uu___87_4491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___87_4491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t5))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____4498 = (

let uu____4499 = (

let uu____4506 = (star_type' env t2)
in ((uu____4506), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____4499))
in (mk1 uu____4498))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inl (t2), FStar_Pervasives_Native.None), something) -> begin
(

let uu____4558 = (

let uu____4559 = (

let uu____4586 = (star_type' env e)
in (

let uu____4589 = (

let uu____4606 = (

let uu____4613 = (star_type' env t2)
in FStar_Util.Inl (uu____4613))
in ((uu____4606), (FStar_Pervasives_Native.None)))
in ((uu____4586), (uu____4589), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4559))
in (mk1 uu____4558))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (FStar_Util.Inr (c), FStar_Pervasives_Native.None), something) -> begin
(

let uu____4695 = (

let uu____4696 = (

let uu____4723 = (star_type' env e)
in (

let uu____4726 = (

let uu____4743 = (

let uu____4750 = (star_type' env (FStar_Syntax_Util.comp_result c))
in FStar_Util.Inl (uu____4750))
in ((uu____4743), (FStar_Pervasives_Native.None)))
in ((uu____4723), (uu____4726), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4696))
in (mk1 uu____4695))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____4785, (uu____4786, FStar_Pervasives_Native.Some (uu____4787)), uu____4788) -> begin
(

let uu____4837 = (

let uu____4842 = (

let uu____4843 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Ascriptions with tactics are outside of the definition language: %s" uu____4843))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4842)))
in (FStar_Errors.raise_err uu____4837))
end
| FStar_Syntax_Syntax.Tm_refine (uu____4844) -> begin
(

let uu____4851 = (

let uu____4856 = (

let uu____4857 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" uu____4857))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4856)))
in (FStar_Errors.raise_err uu____4851))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____4858) -> begin
(

let uu____4865 = (

let uu____4870 = (

let uu____4871 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" uu____4871))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4870)))
in (FStar_Errors.raise_err uu____4865))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____4872) -> begin
(

let uu____4879 = (

let uu____4884 = (

let uu____4885 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_quoted is outside of the definition language: %s" uu____4885))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4884)))
in (FStar_Errors.raise_err uu____4879))
end
| FStar_Syntax_Syntax.Tm_constant (uu____4886) -> begin
(

let uu____4887 = (

let uu____4892 = (

let uu____4893 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" uu____4893))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4892)))
in (FStar_Errors.raise_err uu____4887))
end
| FStar_Syntax_Syntax.Tm_match (uu____4894) -> begin
(

let uu____4917 = (

let uu____4922 = (

let uu____4923 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" uu____4923))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4922)))
in (FStar_Errors.raise_err uu____4917))
end
| FStar_Syntax_Syntax.Tm_let (uu____4924) -> begin
(

let uu____4937 = (

let uu____4942 = (

let uu____4943 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" uu____4943))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4942)))
in (FStar_Errors.raise_err uu____4937))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____4944) -> begin
(

let uu____4945 = (

let uu____4950 = (

let uu____4951 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" uu____4951))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4950)))
in (FStar_Errors.raise_err uu____4945))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____4952 = (

let uu____4957 = (

let uu____4958 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" uu____4958))
in ((FStar_Errors.Fatal_TermOutsideOfDefLanguage), (uu____4957)))
in (FStar_Errors.raise_err uu____4952))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____4960 = (FStar_Syntax_Util.unfold_lazy i)
in (star_type' env uu____4960))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____4963) -> begin
(failwith "impossible")
end)))))


let is_monadic : FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___71_4994 -> (match (uu___71_4994) with
| FStar_Pervasives_Native.None -> begin
(failwith "un-annotated lambda?!")
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___70_5001 -> (match (uu___70_5001) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____5002 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____5008 = (

let uu____5009 = (FStar_Syntax_Subst.compress t)
in uu____5009.FStar_Syntax_Syntax.n)
in (match (uu____5008) with
| FStar_Syntax_Syntax.Tm_app (head1, args) when (FStar_Syntax_Util.is_tuple_constructor head1) -> begin
(

let r = (

let uu____5035 = (

let uu____5036 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5036))
in (is_C uu____5035))
in (match (r) with
| true -> begin
((

let uu____5052 = (

let uu____5053 = (FStar_List.for_all (fun uu____5061 -> (match (uu____5061) with
| (h, uu____5067) -> begin
(is_C h)
end)) args)
in (not (uu____5053)))
in (match (uu____5052) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____5068 -> begin
()
end));
true;
)
end
| uu____5069 -> begin
((

let uu____5071 = (

let uu____5072 = (FStar_List.for_all (fun uu____5081 -> (match (uu____5081) with
| (h, uu____5087) -> begin
(

let uu____5088 = (is_C h)
in (not (uu____5088)))
end)) args)
in (not (uu____5072)))
in (match (uu____5071) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____5089 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____5108 = (nm_of_comp comp.FStar_Syntax_Syntax.n)
in (match (uu____5108) with
| M (t1) -> begin
((

let uu____5111 = (is_C t1)
in (match (uu____5111) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____5112 -> begin
()
end));
true;
)
end
| N (t1) -> begin
(is_C t1)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5115) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5121) -> begin
(is_C t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____5127, uu____5128) -> begin
(is_C t1)
end
| uu____5169 -> begin
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

let uu____5202 = (

let uu____5203 = (

let uu____5218 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5221 = (

let uu____5230 = (

let uu____5235 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (uu____5235)))
in (uu____5230)::[])
in ((uu____5218), (uu____5221))))
in FStar_Syntax_Syntax.Tm_app (uu____5203))
in (mk1 uu____5202))
in (

let uu____5254 = (

let uu____5255 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____5255)::[])
in (FStar_Syntax_Util.abs uu____5254 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___72_5272 -> (match (uu___72_5272) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____5273 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let return_if = (fun uu____5506 -> (match (uu____5506) with
| (rec_nm, s_e, u_e) -> begin
(

let check1 = (fun t1 t2 -> (

let uu____5533 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (

let uu____5535 = (

let uu____5536 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial uu____5536))
in (not (uu____5535))))
in (match (uu____5533) with
| true -> begin
(

let uu____5537 = (

let uu____5542 = (

let uu____5543 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5544 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____5545 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" uu____5543 uu____5544 uu____5545))))
in ((FStar_Errors.Fatal_TypeMismatch), (uu____5542)))
in (FStar_Errors.raise_err uu____5537))
end
| uu____5546 -> begin
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

let uu____5562 = (mk_return env t1 s_e)
in ((M (t1)), (uu____5562), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(

let uu____5569 = (

let uu____5574 = (

let uu____5575 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5576 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____5577 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" uu____5575 uu____5576 uu____5577))))
in ((FStar_Errors.Fatal_EffectfulAndPureComputationMismatch), (uu____5574)))
in (FStar_Errors.raise_err uu____5569))
end))
end))
in (

let ensure_m = (fun env1 e2 -> (

let strip_m = (fun uu___73_5624 -> (match (uu___73_5624) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____5640 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(

let uu____5660 = (

let uu____5665 = (

let uu____5666 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " uu____5666))
in ((FStar_Errors.Fatal_LetBoundMonadicMismatch), (uu____5665)))
in (FStar_Errors.raise_error uu____5660 e2.FStar_Syntax_Syntax.pos))
end
| M (uu____5673) -> begin
(

let uu____5674 = (check env1 e2 context_nm)
in (strip_m uu____5674))
end)))
in (

let uu____5681 = (

let uu____5682 = (FStar_Syntax_Subst.compress e)
in uu____5682.FStar_Syntax_Syntax.n)
in (match (uu____5681) with
| FStar_Syntax_Syntax.Tm_bvar (uu____5691) -> begin
(

let uu____5692 = (infer env e)
in (return_if uu____5692))
end
| FStar_Syntax_Syntax.Tm_name (uu____5699) -> begin
(

let uu____5700 = (infer env e)
in (return_if uu____5700))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5707) -> begin
(

let uu____5708 = (infer env e)
in (return_if uu____5708))
end
| FStar_Syntax_Syntax.Tm_abs (uu____5715) -> begin
(

let uu____5732 = (infer env e)
in (return_if uu____5732))
end
| FStar_Syntax_Syntax.Tm_constant (uu____5739) -> begin
(

let uu____5740 = (infer env e)
in (return_if uu____5740))
end
| FStar_Syntax_Syntax.Tm_quoted (uu____5747) -> begin
(

let uu____5754 = (infer env e)
in (return_if uu____5754))
end
| FStar_Syntax_Syntax.Tm_app (uu____5761) -> begin
(

let uu____5776 = (infer env e)
in (return_if uu____5776))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____5784 = (FStar_Syntax_Util.unfold_lazy i)
in (check env uu____5784 context_nm))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env1 e21 -> (check env1 e21 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env1 body -> (check env1 body context_nm)))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____5846) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____5852) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____5858, uu____5859) -> begin
(check env e1 context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____5900) -> begin
(

let uu____5913 = (

let uu____5914 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" uu____5914))
in (failwith uu____5913))
end
| FStar_Syntax_Syntax.Tm_type (uu____5921) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5928) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____5947) -> begin
(

let uu____5954 = (

let uu____5955 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" uu____5955))
in (failwith uu____5954))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5962) -> begin
(

let uu____5963 = (

let uu____5964 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" uu____5964))
in (failwith uu____5963))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____5971) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6002 = (

let uu____6003 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" uu____6003))
in (failwith uu____6002))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let normalize1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (

let uu____6031 = (

let uu____6032 = (FStar_Syntax_Subst.compress e)
in uu____6032.FStar_Syntax_Syntax.n)
in (match (uu____6031) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____6050 = (FStar_Syntax_Util.unfold_lazy i)
in (infer env uu____6050))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) -> begin
(

let subst_rc_opt = (fun subst1 rc_opt1 -> (match (rc_opt1) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = uu____6097; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = uu____6098}) -> begin
rc_opt1
end
| FStar_Pervasives_Native.None -> begin
rc_opt1
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____6104 = (

let uu___88_6105 = rc
in (

let uu____6106 = (

let uu____6111 = (

let uu____6114 = (FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ)
in (FStar_Syntax_Subst.subst subst1 uu____6114))
in FStar_Pervasives_Native.Some (uu____6111))
in {FStar_Syntax_Syntax.residual_effect = uu___88_6105.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6106; FStar_Syntax_Syntax.residual_flags = uu___88_6105.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____6104))
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

let uu___89_6126 = env
in (

let uu____6127 = (FStar_TypeChecker_Env.push_binders env.env binders1)
in {env = uu____6127; subst = uu___89_6126.subst; tc_const = uu___89_6126.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____6147 -> (match (uu____6147) with
| (bv, qual) -> begin
(

let sort = (star_type' env1 bv.FStar_Syntax_Syntax.sort)
in (((

let uu___90_6160 = bv
in {FStar_Syntax_Syntax.ppname = uu___90_6160.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___90_6160.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders1)
in (

let uu____6161 = (FStar_List.fold_left (fun uu____6190 uu____6191 -> (match (((uu____6190), (uu____6191))) with
| ((env2, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____6239 = (is_C c)
in (match (uu____6239) with
| true -> begin
(

let xw = (

let uu____6247 = (star_type' env2 c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w") FStar_Pervasives_Native.None uu____6247))
in (

let x = (

let uu___91_6249 = bv
in (

let uu____6250 = (

let uu____6253 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env2 c uu____6253))
in {FStar_Syntax_Syntax.ppname = uu___91_6249.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___91_6249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6250}))
in (

let env3 = (

let uu___92_6255 = env2
in (

let uu____6256 = (

let uu____6259 = (

let uu____6260 = (

let uu____6267 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (uu____6267)))
in FStar_Syntax_Syntax.NT (uu____6260))
in (uu____6259)::env2.subst)
in {env = uu___92_6255.env; subst = uu____6256; tc_const = uu___92_6255.tc_const}))
in (

let uu____6272 = (

let uu____6275 = (FStar_Syntax_Syntax.mk_binder x)
in (

let uu____6276 = (

let uu____6279 = (FStar_Syntax_Syntax.mk_binder xw)
in (uu____6279)::acc)
in (uu____6275)::uu____6276))
in ((env3), (uu____6272))))))
end
| uu____6282 -> begin
(

let x = (

let uu___93_6284 = bv
in (

let uu____6285 = (star_type' env2 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___93_6284.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___93_6284.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6285}))
in (

let uu____6288 = (

let uu____6291 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6291)::acc)
in ((env2), (uu____6288))))
end)))
end)) ((env1), ([])) binders1)
in (match (uu____6161) with
| (env2, u_binders) -> begin
(

let u_binders1 = (FStar_List.rev u_binders)
in (

let uu____6311 = (

let check_what = (

let uu____6337 = (is_monadic rc_opt1)
in (match (uu____6337) with
| true -> begin
check_m
end
| uu____6352 -> begin
check_n
end))
in (

let uu____6353 = (check_what env2 body1)
in (match (uu____6353) with
| (t, s_body, u_body) -> begin
(

let uu____6377 = (

let uu____6378 = (

let uu____6379 = (is_monadic rc_opt1)
in (match (uu____6379) with
| true -> begin
M (t)
end
| uu____6380 -> begin
N (t)
end))
in (comp_of_nm uu____6378))
in ((uu____6377), (s_body), (u_body)))
end)))
in (match (uu____6311) with
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

let uu____6410 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___74_6414 -> (match (uu___74_6414) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____6415 -> begin
false
end))))
in (match (uu____6410) with
| true -> begin
(

let uu____6416 = (FStar_List.filter (fun uu___75_6420 -> (match (uu___75_6420) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____6421 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None uu____6416))
end
| uu____6424 -> begin
rc
end))
in FStar_Pervasives_Native.Some (rc1))
end
| FStar_Pervasives_Native.Some (rt) -> begin
(

let uu____6430 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_Util.for_some (fun uu___76_6434 -> (match (uu___76_6434) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____6435 -> begin
false
end))))
in (match (uu____6430) with
| true -> begin
(

let flags1 = (FStar_List.filter (fun uu___77_6442 -> (match (uu___77_6442) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____6443 -> begin
true
end)) rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____6444 = (

let uu____6445 = (

let uu____6450 = (double_star rt)
in FStar_Pervasives_Native.Some (uu____6450))
in (FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid uu____6445 flags1))
in FStar_Pervasives_Native.Some (uu____6444)))
end
| uu____6455 -> begin
(

let uu____6456 = (

let uu___94_6457 = rc
in (

let uu____6458 = (

let uu____6463 = (star_type' env2 rt)
in FStar_Pervasives_Native.Some (uu____6463))
in {FStar_Syntax_Syntax.residual_effect = uu___94_6457.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6458; FStar_Syntax_Syntax.residual_flags = uu___94_6457.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____6456))
end))
end)
end)
in (

let uu____6468 = (

let comp1 = (

let uu____6478 = (is_monadic rc_opt1)
in (

let uu____6479 = (FStar_Syntax_Subst.subst env2.subst s_body)
in (trans_G env2 (FStar_Syntax_Util.comp_result comp) uu____6478 uu____6479)))
in (

let uu____6480 = (FStar_Syntax_Util.ascribe u_body ((FStar_Util.Inr (comp1)), (FStar_Pervasives_Native.None)))
in ((uu____6480), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp1))))))
in (match (uu____6468) with
| (u_body1, u_rc_opt) -> begin
(

let s_body1 = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders1 = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (

let uu____6524 = (

let uu____6525 = (

let uu____6542 = (

let uu____6545 = (FStar_Syntax_Subst.closing_of_binders s_binders1)
in (subst_rc_opt uu____6545 s_rc_opt))
in ((s_binders1), (s_body1), (uu____6542)))
in FStar_Syntax_Syntax.Tm_abs (uu____6525))
in (mk1 uu____6524))
in (

let u_body2 = (FStar_Syntax_Subst.close u_binders1 u_body1)
in (

let u_binders2 = (FStar_Syntax_Subst.close_binders u_binders1)
in (

let u_term = (

let uu____6563 = (

let uu____6564 = (

let uu____6581 = (

let uu____6584 = (FStar_Syntax_Subst.closing_of_binders u_binders2)
in (subst_rc_opt uu____6584 u_rc_opt))
in ((u_binders2), (u_body2), (uu____6581)))
in FStar_Syntax_Syntax.Tm_abs (uu____6564))
in (mk1 uu____6563))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.p = uu____6598}; FStar_Syntax_Syntax.fv_delta = uu____6599; FStar_Syntax_Syntax.fv_qual = uu____6600}) -> begin
(

let uu____6603 = (

let uu____6608 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6608))
in (match (uu____6603) with
| (uu____6639, t) -> begin
(

let uu____6641 = (

let uu____6642 = (normalize1 t)
in N (uu____6642))
in ((uu____6641), (e), (e)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____6643; FStar_Syntax_Syntax.vars = uu____6644}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____6707 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____6707) with
| (unary_op, uu____6729) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____6788; FStar_Syntax_Syntax.vars = uu____6789}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____6865 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____6865) with
| (unary_op, uu____6887) -> begin
(

let head1 = (mk1 (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a1)::(a2)::[])))))
in (

let t = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))))
in (infer env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____6952; FStar_Syntax_Syntax.vars = uu____6953}, ((a, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____6983 = (infer env a)
in (match (uu____6983) with
| (t, s, u) -> begin
(

let uu____6999 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____6999) with
| (head1, uu____7021) -> begin
(

let uu____7042 = (

let uu____7043 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in N (uu____7043))
in (

let uu____7044 = (

let uu____7045 = (

let uu____7046 = (

let uu____7061 = (

let uu____7070 = (FStar_Syntax_Syntax.as_arg s)
in (uu____7070)::[])
in ((head1), (uu____7061)))
in FStar_Syntax_Syntax.Tm_app (uu____7046))
in (mk1 uu____7045))
in (

let uu____7081 = (

let uu____7082 = (

let uu____7083 = (

let uu____7098 = (

let uu____7107 = (FStar_Syntax_Syntax.as_arg u)
in (uu____7107)::[])
in ((head1), (uu____7098)))
in FStar_Syntax_Syntax.Tm_app (uu____7083))
in (mk1 uu____7082))
in ((uu____7042), (uu____7044), (uu____7081)))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____7118; FStar_Syntax_Syntax.vars = uu____7119}, ((a1, uu____7121))::(a2)::[]) -> begin
(

let uu____7163 = (infer env a1)
in (match (uu____7163) with
| (t, s, u) -> begin
(

let uu____7179 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____7179) with
| (head1, uu____7201) -> begin
(

let uu____7222 = (

let uu____7223 = (

let uu____7224 = (

let uu____7239 = (

let uu____7248 = (FStar_Syntax_Syntax.as_arg s)
in (uu____7248)::(a2)::[])
in ((head1), (uu____7239)))
in FStar_Syntax_Syntax.Tm_app (uu____7224))
in (mk1 uu____7223))
in (

let uu____7259 = (

let uu____7260 = (

let uu____7261 = (

let uu____7276 = (

let uu____7285 = (FStar_Syntax_Syntax.as_arg u)
in (uu____7285)::(a2)::[])
in ((head1), (uu____7276)))
in FStar_Syntax_Syntax.Tm_app (uu____7261))
in (mk1 uu____7260))
in ((t), (uu____7222), (uu____7259))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____7296; FStar_Syntax_Syntax.vars = uu____7297}, uu____7298) -> begin
(

let uu____7319 = (

let uu____7324 = (

let uu____7325 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7325))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____7324)))
in (FStar_Errors.raise_error uu____7319 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____7332; FStar_Syntax_Syntax.vars = uu____7333}, uu____7334) -> begin
(

let uu____7355 = (

let uu____7360 = (

let uu____7361 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7361))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____7360)))
in (FStar_Errors.raise_error uu____7355 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____7390 = (check_n env head1)
in (match (uu____7390) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____7412 = (

let uu____7413 = (FStar_Syntax_Subst.compress t)
in uu____7413.FStar_Syntax_Syntax.n)
in (match (uu____7412) with
| FStar_Syntax_Syntax.Tm_arrow (uu____7416) -> begin
true
end
| uu____7429 -> begin
false
end)))
in (

let rec flatten1 = (fun t -> (

let uu____7448 = (

let uu____7449 = (FStar_Syntax_Subst.compress t)
in uu____7449.FStar_Syntax_Syntax.n)
in (match (uu____7448) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t1, uu____7466); FStar_Syntax_Syntax.pos = uu____7467; FStar_Syntax_Syntax.vars = uu____7468}) when (is_arrow t1) -> begin
(

let uu____7493 = (flatten1 t1)
in (match (uu____7493) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____7575, uu____7576) -> begin
(flatten1 e1)
end
| uu____7617 -> begin
(

let uu____7618 = (

let uu____7623 = (

let uu____7624 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" uu____7624))
in ((FStar_Errors.Fatal_NotFunctionType), (uu____7623)))
in (FStar_Errors.raise_err uu____7618))
end)))
in (

let uu____7637 = (flatten1 t_head)
in (match (uu____7637) with
| (binders, comp) -> begin
(

let n1 = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(

let uu____7697 = (

let uu____7702 = (

let uu____7703 = (FStar_Util.string_of_int n1)
in (

let uu____7710 = (FStar_Util.string_of_int (n' - n1))
in (

let uu____7721 = (FStar_Util.string_of_int n1)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." uu____7703 uu____7710 uu____7721))))
in ((FStar_Errors.Fatal_BinderAndArgsLengthMismatch), (uu____7702)))
in (FStar_Errors.raise_err uu____7697))
end
| uu____7728 -> begin
()
end);
(

let uu____7729 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____7729) with
| (binders1, comp1) -> begin
(

let rec final_type = (fun subst1 uu____7778 args1 -> (match (uu____7778) with
| (binders2, comp2) -> begin
(match (((binders2), (args1))) with
| ([], []) -> begin
(

let uu____7858 = (

let uu____7859 = (FStar_Syntax_Subst.subst_comp subst1 comp2)
in uu____7859.FStar_Syntax_Syntax.n)
in (nm_of_comp uu____7858))
end
| (binders3, []) -> begin
(

let uu____7889 = (

let uu____7890 = (

let uu____7893 = (

let uu____7894 = (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders3), (comp2)))))
in (FStar_Syntax_Subst.subst subst1 uu____7894))
in (FStar_Syntax_Subst.compress uu____7893))
in uu____7890.FStar_Syntax_Syntax.n)
in (match (uu____7889) with
| FStar_Syntax_Syntax.Tm_arrow (binders4, comp3) -> begin
(

let uu____7921 = (

let uu____7922 = (

let uu____7923 = (

let uu____7936 = (FStar_Syntax_Subst.close_comp binders4 comp3)
in ((binders4), (uu____7936)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7923))
in (mk1 uu____7922))
in N (uu____7921))
end
| uu____7947 -> begin
(failwith "wat?")
end))
end
| ([], (uu____7948)::uu____7949) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____7989))::binders3, ((arg, uu____7992))::args2) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst1) ((binders3), (comp2)) args2)
end)
end))
in (

let final_type1 = (final_type [] ((binders1), (comp1)) args)
in (

let uu____8055 = (FStar_List.splitAt n' binders1)
in (match (uu____8055) with
| (binders2, uu____8087) -> begin
(

let uu____8112 = (

let uu____8131 = (FStar_List.map2 (fun uu____8179 uu____8180 -> (match (((uu____8179), (uu____8180))) with
| ((bv, uu____8212), (arg, q)) -> begin
(

let uu____8223 = (

let uu____8224 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in uu____8224.FStar_Syntax_Syntax.n)
in (match (uu____8223) with
| FStar_Syntax_Syntax.Tm_type (uu____8241) -> begin
(

let uu____8242 = (

let uu____8247 = (star_type' env arg)
in ((uu____8247), (q)))
in ((uu____8242), ((((arg), (q)))::[])))
end
| uu____8266 -> begin
(

let uu____8267 = (check_n env arg)
in (match (uu____8267) with
| (uu____8288, s_arg, u_arg) -> begin
(

let uu____8291 = (

let uu____8298 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____8298) with
| true -> begin
(

let uu____8305 = (

let uu____8310 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((uu____8310), (q)))
in (uu____8305)::(((u_arg), (q)))::[])
end
| uu____8323 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (uu____8291)))
end))
end))
end)) binders2 args)
in (FStar_List.split uu____8131))
in (match (uu____8112) with
| (s_args, u_args) -> begin
(

let u_args1 = (FStar_List.flatten u_args)
in (

let uu____8399 = (mk1 (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (

let uu____8410 = (mk1 (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args1)))))
in ((final_type1), (uu____8399), (uu____8410)))))
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
| FStar_Syntax_Syntax.Tm_uinst (e1, uu____8474) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____8480) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, uu____8486, uu____8487) -> begin
(infer env e1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____8529 = (

let uu____8530 = (env.tc_const c)
in N (uu____8530))
in ((uu____8529), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qt) -> begin
((N (FStar_Syntax_Syntax.t_term)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_let (uu____8537) -> begin
(

let uu____8550 = (

let uu____8551 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" uu____8551))
in (failwith uu____8550))
end
| FStar_Syntax_Syntax.Tm_type (uu____8558) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____8565) -> begin
(failwith "impossible (DM stratification)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____8584) -> begin
(

let uu____8591 = (

let uu____8592 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" uu____8592))
in (failwith uu____8591))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____8599) -> begin
(

let uu____8600 = (

let uu____8601 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8601))
in (failwith uu____8600))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____8608) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____8639 = (

let uu____8640 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8640))
in (failwith uu____8639))
end)))))
and mk_match : env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None e0.FStar_Syntax_Syntax.pos))
in (

let uu____8687 = (check_n env e0)
in (match (uu____8687) with
| (uu____8700, s_e0, u_e0) -> begin
(

let uu____8703 = (

let uu____8732 = (FStar_List.map (fun b -> (

let uu____8793 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____8793) with
| (pat, FStar_Pervasives_Native.None, body) -> begin
(

let env1 = (

let uu___95_8835 = env
in (

let uu____8836 = (

let uu____8837 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env uu____8837))
in {env = uu____8836; subst = uu___95_8835.subst; tc_const = uu___95_8835.tc_const}))
in (

let uu____8840 = (f env1 body)
in (match (uu____8840) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (FStar_Pervasives_Native.None), (((s_body), (u_body), (body))))))
end)))
end
| uu____8912 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_WhenClauseNotSupported), ("No when clauses in the definition language")))
end))) branches)
in (FStar_List.split uu____8732))
in (match (uu____8703) with
| (nms, branches1) -> begin
(

let t1 = (

let uu____9016 = (FStar_List.hd nms)
in (match (uu____9016) with
| M (t1) -> begin
t1
end
| N (t1) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___78_9024 -> (match (uu___78_9024) with
| M (uu____9025) -> begin
true
end
| uu____9026 -> begin
false
end)) nms)
in (

let uu____9027 = (

let uu____9064 = (FStar_List.map2 (fun nm uu____9154 -> (match (uu____9154) with
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

let uu____9331 = (check env original_body (M (t2)))
in (match (uu____9331) with
| (uu____9368, s_body1, u_body1) -> begin
((M (t2)), (((pat), (guard), (s_body1))), (((pat), (guard), (u_body1))))
end))
end
| (M (uu____9407), false) -> begin
(failwith "impossible")
end)
end)) nms branches1)
in (FStar_List.unzip3 uu____9064))
in (match (uu____9027) with
| (nms1, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk1 env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_branches1 = (FStar_List.map (fun uu____9591 -> (match (uu____9591) with
| (pat, guard, s_body) -> begin
(

let s_body1 = (

let uu____9642 = (

let uu____9643 = (

let uu____9658 = (

let uu____9667 = (

let uu____9672 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____9673 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____9672), (uu____9673))))
in (uu____9667)::[])
in ((s_body), (uu____9658)))
in FStar_Syntax_Syntax.Tm_app (uu____9643))
in (mk1 uu____9642))
in ((pat), (guard), (s_body1)))
end)) s_branches)
in (

let s_branches2 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches1)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (

let uu____9735 = (

let uu____9736 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____9736)::[])
in (

let uu____9749 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches2)))))
in (FStar_Syntax_Util.abs uu____9735 uu____9749 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))))
in (

let t1_star = (

let uu____9773 = (

let uu____9780 = (

let uu____9785 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____9785))
in (uu____9780)::[])
in (

let uu____9798 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____9773 uu____9798)))
in (

let uu____9801 = (mk1 (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))))
in (

let uu____9840 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((M (t1)), (uu____9801), (uu____9840)))))))))))
end
| uu____9859 -> begin
(

let s_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches1 = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (

let uu____9893 = (

let uu____9894 = (

let uu____9895 = (

let uu____9922 = (mk1 (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches1)))))
in ((uu____9922), (((FStar_Util.Inl (t1_star)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____9895))
in (mk1 uu____9894))
in (

let uu____9981 = (mk1 (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches1)))))
in ((N (t1)), (uu____9893), (uu____9981)))))))
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

let uu____10044 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____10044)::[])
in (

let uu____10057 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____10057) with
| (x_binders1, e21) -> begin
(

let uu____10070 = (infer env e1)
in (match (uu____10070) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____10087 = (is_C t1)
in (match (uu____10087) with
| true -> begin
(

let uu___96_10088 = binding
in (

let uu____10089 = (

let uu____10092 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 uu____10092))
in {FStar_Syntax_Syntax.lbname = uu___96_10088.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___96_10088.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____10089; FStar_Syntax_Syntax.lbeff = uu___96_10088.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___96_10088.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___96_10088.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___96_10088.FStar_Syntax_Syntax.lbpos}))
end
| uu____10093 -> begin
binding
end))
in (

let env1 = (

let uu___97_10095 = env
in (

let uu____10096 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___98_10098 = x
in {FStar_Syntax_Syntax.ppname = uu___98_10098.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___98_10098.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____10096; subst = uu___97_10095.subst; tc_const = uu___97_10095.tc_const}))
in (

let uu____10099 = (proceed env1 e21)
in (match (uu____10099) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___99_10116 = binding
in (

let uu____10117 = (star_type' env1 binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___99_10116.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___99_10116.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____10117; FStar_Syntax_Syntax.lbeff = uu___99_10116.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___99_10116.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___99_10116.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___99_10116.FStar_Syntax_Syntax.lbpos}))
in (

let uu____10120 = (

let uu____10121 = (

let uu____10122 = (

let uu____10135 = (FStar_Syntax_Subst.close x_binders1 s_e2)
in ((((false), (((

let uu___100_10149 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___100_10149.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___100_10149.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___100_10149.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___100_10149.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1; FStar_Syntax_Syntax.lbattrs = uu___100_10149.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___100_10149.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____10135)))
in FStar_Syntax_Syntax.Tm_let (uu____10122))
in (mk1 uu____10121))
in (

let uu____10150 = (

let uu____10151 = (

let uu____10152 = (

let uu____10165 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___101_10179 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___101_10179.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___101_10179.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___101_10179.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___101_10179.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___101_10179.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___101_10179.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____10165)))
in FStar_Syntax_Syntax.Tm_let (uu____10152))
in (mk1 uu____10151))
in ((nm_rec), (uu____10120), (uu____10150)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___102_10184 = binding
in {FStar_Syntax_Syntax.lbname = uu___102_10184.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___102_10184.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___102_10184.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___102_10184.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___102_10184.FStar_Syntax_Syntax.lbpos})
in (

let env1 = (

let uu___103_10186 = env
in (

let uu____10187 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___104_10189 = x
in {FStar_Syntax_Syntax.ppname = uu___104_10189.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_10189.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____10187; subst = uu___103_10186.subst; tc_const = uu___103_10186.tc_const}))
in (

let uu____10190 = (ensure_m env1 e21)
in (match (uu____10190) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk1 env1 t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" FStar_Pervasives_Native.None p_type)
in (

let s_e21 = (

let uu____10213 = (

let uu____10214 = (

let uu____10229 = (

let uu____10238 = (

let uu____10243 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____10244 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____10243), (uu____10244))))
in (uu____10238)::[])
in ((s_e2), (uu____10229)))
in FStar_Syntax_Syntax.Tm_app (uu____10214))
in (mk1 uu____10213))
in (

let s_e22 = (FStar_Syntax_Util.abs x_binders1 s_e21 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))))
in (

let body = (

let uu____10269 = (

let uu____10270 = (

let uu____10285 = (

let uu____10294 = (

let uu____10301 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e22), (uu____10301)))
in (uu____10294)::[])
in ((s_e1), (uu____10285)))
in FStar_Syntax_Syntax.Tm_app (uu____10270))
in (mk1 uu____10269))
in (

let uu____10326 = (

let uu____10327 = (

let uu____10328 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____10328)::[])
in (FStar_Syntax_Util.abs uu____10327 body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)))))
in (

let uu____10341 = (

let uu____10342 = (

let uu____10343 = (

let uu____10356 = (FStar_Syntax_Subst.close x_binders1 u_e2)
in ((((false), (((

let uu___105_10370 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___105_10370.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___105_10370.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___105_10370.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___105_10370.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1; FStar_Syntax_Syntax.lbattrs = uu___105_10370.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___105_10370.FStar_Syntax_Syntax.lbpos}))::[]))), (uu____10356)))
in FStar_Syntax_Syntax.Tm_let (uu____10343))
in (mk1 uu____10342))
in ((M (t2)), (uu____10326), (uu____10341)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____10380 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in N (uu____10380))
in (

let uu____10381 = (check env e mn)
in (match (uu____10381) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____10397 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____10419 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in M (uu____10419))
in (

let uu____10420 = (check env e mn)
in (match (uu____10420) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____10436 -> begin
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

let uu____10466 = (

let uu____10467 = (is_C c)
in (not (uu____10467)))
in (match (uu____10466) with
| true -> begin
(failwith "not a C")
end
| uu____10468 -> begin
()
end));
(

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (

let uu____10477 = (

let uu____10478 = (FStar_Syntax_Subst.compress c)
in uu____10478.FStar_Syntax_Syntax.n)
in (match (uu____10477) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____10503 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____10503) with
| (wp_head, wp_args) -> begin
((

let uu____10541 = ((not ((Prims.op_Equality (FStar_List.length wp_args) (FStar_List.length args)))) || (

let uu____10555 = (

let uu____10556 = (FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head uu____10556))
in (not (uu____10555))))
in (match (uu____10541) with
| true -> begin
(failwith "mismatch")
end
| uu____10563 -> begin
()
end));
(

let uu____10564 = (

let uu____10565 = (

let uu____10580 = (FStar_List.map2 (fun uu____10610 uu____10611 -> (match (((uu____10610), (uu____10611))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q1 -> (

let uu____10650 = (FStar_Syntax_Syntax.is_implicit q1)
in (match (uu____10650) with
| true -> begin
"implicit"
end
| uu____10651 -> begin
"explicit"
end)))
in ((match ((Prims.op_disEquality q q')) with
| true -> begin
(

let uu____10653 = (

let uu____10658 = (

let uu____10659 = (print_implicit q)
in (

let uu____10660 = (print_implicit q')
in (FStar_Util.format2 "Incoherent implicit qualifiers %b %b\n" uu____10659 uu____10660)))
in ((FStar_Errors.Warning_IncoherentImplicitQualifier), (uu____10658)))
in (FStar_Errors.log_issue head1.FStar_Syntax_Syntax.pos uu____10653))
end
| uu____10661 -> begin
()
end);
(

let uu____10662 = (trans_F_ env arg wp_arg)
in ((uu____10662), (q)));
))
end)) args wp_args)
in ((head1), (uu____10580)))
in FStar_Syntax_Syntax.Tm_app (uu____10565))
in (mk1 uu____10564));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders1 = (FStar_Syntax_Util.name_binders binders)
in (

let uu____10698 = (FStar_Syntax_Subst.open_comp binders1 comp)
in (match (uu____10698) with
| (binders_orig, comp1) -> begin
(

let uu____10705 = (

let uu____10720 = (FStar_List.map (fun uu____10754 -> (match (uu____10754) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____10774 = (is_C h)
in (match (uu____10774) with
| true -> begin
(

let w' = (

let uu____10786 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__w\'") FStar_Pervasives_Native.None uu____10786))
in (

let uu____10787 = (

let uu____10794 = (

let uu____10801 = (

let uu____10806 = (

let uu____10807 = (

let uu____10808 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h uu____10808))
in (FStar_Syntax_Syntax.null_bv uu____10807))
in ((uu____10806), (q)))
in (uu____10801)::[])
in (((w'), (q)))::uu____10794)
in ((w'), (uu____10787))))
end
| uu____10827 -> begin
(

let x = (

let uu____10829 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "__x") FStar_Pervasives_Native.None uu____10829))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig)
in (FStar_List.split uu____10720))
in (match (uu____10705) with
| (bvs, binders2) -> begin
(

let binders3 = (FStar_List.flatten binders2)
in (

let comp2 = (

let uu____10884 = (

let uu____10887 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig uu____10887))
in (FStar_Syntax_Subst.subst_comp uu____10884 comp1))
in (

let app = (

let uu____10891 = (

let uu____10892 = (

let uu____10907 = (FStar_List.map (fun bv -> (

let uu____10924 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____10925 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____10924), (uu____10925))))) bvs)
in ((wp), (uu____10907)))
in FStar_Syntax_Syntax.Tm_app (uu____10892))
in (mk1 uu____10891))
in (

let comp3 = (

let uu____10937 = (type_of_comp comp2)
in (

let uu____10938 = (is_monadic_comp comp2)
in (trans_G env uu____10937 uu____10938 app)))
in (FStar_Syntax_Util.arrow binders3 comp3)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____10940, uu____10941) -> begin
(trans_F_ env e wp)
end
| uu____10982 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic1 wp -> (match (is_monadic1) with
| true -> begin
(

let uu____10987 = (

let uu____10988 = (star_type' env h)
in (

let uu____10991 = (

let uu____11000 = (

let uu____11007 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (uu____11007)))
in (uu____11000)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu____10988; FStar_Syntax_Syntax.effect_args = uu____10991; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____10987))
end
| uu____11022 -> begin
(

let uu____11023 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total uu____11023))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____11042 = (n env.env t)
in (star_type' env uu____11042)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (

let uu____11061 = (n env.env t)
in (check_n env uu____11061)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let uu____11077 = (n env.env c)
in (

let uu____11078 = (n env.env wp)
in (trans_F_ env uu____11077 uu____11078))))




