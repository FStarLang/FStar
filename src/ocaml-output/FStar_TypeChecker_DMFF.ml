
open Prims
type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let uu___93_64 = a
in (

let uu____65 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___93_64.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___93_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____65}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in ((

let uu____73 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____73) with
| true -> begin
((d "Elaborating extra WP combinators");
(

let uu____75 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" uu____75));
)
end
| uu____76 -> begin
()
end));
(

let rec collect_binders = (fun t -> (

let uu____84 = (

let uu____85 = (

let uu____88 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____88))
in uu____85.FStar_Syntax_Syntax.n)
in (match (uu____84) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____110) -> begin
t
end
| uu____117 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (

let uu____120 = (collect_binders rest)
in (FStar_List.append bs uu____120)))
end
| FStar_Syntax_Syntax.Tm_type (uu____126) -> begin
[]
end
| uu____129 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (

let uu____141 = (collect_binders wp_a)
in (FStar_All.pipe_right uu____141 FStar_Syntax_Util.name_binders))
in ((

let uu____152 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____152) with
| true -> begin
(

let uu____153 = (

let uu____154 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" uu____154))
in (d uu____153))
end
| uu____155 -> begin
()
end));
(

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange))
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let register = (fun env lident def -> (

let uu____186 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (uu____186) with
| (sigelt, fv) -> begin
((

let uu____192 = (

let uu____194 = (FStar_ST.read sigelts)
in (sigelt)::uu____194)
in (FStar_ST.write sigelts uu____192));
fv;
)
end)))
in (

let binders_of_list = (FStar_List.map (fun uu____215 -> (match (uu____215) with
| (t, b) -> begin
(

let uu____222 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (uu____222)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (

let uu____239 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (uu____239)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (

let uu____252 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg uu____252))))
in (

let uu____253 = (

let uu____265 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (

let uu____285 = (f (FStar_Syntax_Syntax.bv_to_name t))
in (FStar_Syntax_Util.arrow gamma uu____285))
in (

let uu____288 = (

let uu____292 = (

let uu____296 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____297 = (

let uu____299 = (FStar_Syntax_Syntax.mk_binder t)
in (uu____299)::[])
in (uu____296)::uu____297))
in (FStar_List.append binders uu____292))
in (FStar_Syntax_Util.abs uu____288 body None)))))
in (

let uu____307 = (mk FStar_Syntax_Syntax.mk_Total)
in (

let uu____308 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((uu____307), (uu____308)))))
in (match (uu____265) with
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

let mk_app = (fun fv t -> (

let uu____339 = (

let uu____340 = (

let uu____350 = (

let uu____354 = (FStar_List.map (fun uu____362 -> (match (uu____362) with
| (bv, uu____368) -> begin
(

let uu____369 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____370 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____369), (uu____370))))
end)) binders)
in (

let uu____371 = (

let uu____375 = (

let uu____378 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____379 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____378), (uu____379))))
in (

let uu____380 = (

let uu____384 = (

let uu____387 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (uu____387)))
in (uu____384)::[])
in (uu____375)::uu____380))
in (FStar_List.append uu____354 uu____371)))
in ((fv), (uu____350)))
in FStar_Syntax_Syntax.Tm_app (uu____340))
in (mk uu____339)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (uu____253) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (

let uu____433 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None uu____433))
in (

let ret = (

let uu____441 = (

let uu____447 = (

let uu____448 = (

let uu____451 = (

let uu____452 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx uu____452))
in (FStar_Syntax_Syntax.mk_Total uu____451))
in (FStar_Syntax_Util.lcomp_of_comp uu____448))
in FStar_Util.Inl (uu____447))
in Some (uu____441))
in (

let body = (

let uu____462 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma uu____462 ret))
in (

let uu____463 = (

let uu____467 = (mk_all_implicit binders)
in (

let uu____471 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append uu____467 uu____471)))
in (FStar_Syntax_Util.abs uu____463 body ret))))))
in (

let c_pure = (

let uu____486 = (mk_lid "pure")
in (register env uu____486 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (

let uu____491 = (

let uu____492 = (

let uu____493 = (

let uu____497 = (

let uu____498 = (

let uu____499 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None uu____499))
in (FStar_Syntax_Syntax.mk_binder uu____498))
in (uu____497)::[])
in (

let uu____500 = (

let uu____503 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____503))
in (FStar_Syntax_Util.arrow uu____493 uu____500)))
in (mk_gctx uu____492))
in (FStar_Syntax_Syntax.gen_bv "l" None uu____491))
in (

let r = (

let uu____505 = (

let uu____506 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____506))
in (FStar_Syntax_Syntax.gen_bv "r" None uu____505))
in (

let ret = (

let uu____514 = (

let uu____520 = (

let uu____521 = (

let uu____524 = (

let uu____525 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____525))
in (FStar_Syntax_Syntax.mk_Total uu____524))
in (FStar_Syntax_Util.lcomp_of_comp uu____521))
in FStar_Util.Inl (uu____520))
in Some (uu____514))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (

let uu____540 = (FStar_Syntax_Syntax.bv_to_name l)
in (

let uu____543 = (

let uu____549 = (

let uu____551 = (

let uu____552 = (

let uu____553 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app uu____553 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg uu____552))
in (uu____551)::[])
in (FStar_List.append gamma_as_args uu____549))
in (FStar_Syntax_Util.mk_app uu____540 uu____543)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (

let uu____556 = (

let uu____560 = (mk_all_implicit binders)
in (

let uu____564 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append uu____560 uu____564)))
in (FStar_Syntax_Util.abs uu____556 outer_body ret))))))))
in (

let c_app = (

let uu____583 = (mk_lid "app")
in (register env uu____583 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____590 = (

let uu____594 = (

let uu____595 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____595))
in (uu____594)::[])
in (

let uu____596 = (

let uu____599 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____599))
in (FStar_Syntax_Util.arrow uu____590 uu____596)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (

let uu____602 = (

let uu____603 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____603))
in (FStar_Syntax_Syntax.gen_bv "a1" None uu____602))
in (

let ret = (

let uu____611 = (

let uu____617 = (

let uu____618 = (

let uu____621 = (

let uu____622 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____622))
in (FStar_Syntax_Syntax.mk_Total uu____621))
in (FStar_Syntax_Util.lcomp_of_comp uu____618))
in FStar_Util.Inl (uu____617))
in Some (uu____611))
in (

let uu____631 = (

let uu____635 = (mk_all_implicit binders)
in (

let uu____639 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append uu____635 uu____639)))
in (

let uu____657 = (

let uu____658 = (

let uu____664 = (

let uu____666 = (

let uu____669 = (

let uu____675 = (

let uu____677 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____677)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____675))
in (FStar_Syntax_Util.mk_app c_pure uu____669))
in (

let uu____678 = (

let uu____682 = (FStar_Syntax_Syntax.bv_to_name a1)
in (uu____682)::[])
in (uu____666)::uu____678))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____664))
in (FStar_Syntax_Util.mk_app c_app uu____658))
in (FStar_Syntax_Util.abs uu____631 uu____657 ret)))))))))
in (

let c_lift1 = (

let uu____686 = (mk_lid "lift1")
in (register env uu____686 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____694 = (

let uu____698 = (

let uu____699 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____699))
in (

let uu____700 = (

let uu____702 = (

let uu____703 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder uu____703))
in (uu____702)::[])
in (uu____698)::uu____700))
in (

let uu____704 = (

let uu____707 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal uu____707))
in (FStar_Syntax_Util.arrow uu____694 uu____704)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (

let uu____710 = (

let uu____711 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx uu____711))
in (FStar_Syntax_Syntax.gen_bv "a1" None uu____710))
in (

let a2 = (

let uu____713 = (

let uu____714 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____714))
in (FStar_Syntax_Syntax.gen_bv "a2" None uu____713))
in (

let ret = (

let uu____722 = (

let uu____728 = (

let uu____729 = (

let uu____732 = (

let uu____733 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx uu____733))
in (FStar_Syntax_Syntax.mk_Total uu____732))
in (FStar_Syntax_Util.lcomp_of_comp uu____729))
in FStar_Util.Inl (uu____728))
in Some (uu____722))
in (

let uu____742 = (

let uu____746 = (mk_all_implicit binders)
in (

let uu____750 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append uu____746 uu____750)))
in (

let uu____772 = (

let uu____773 = (

let uu____779 = (

let uu____781 = (

let uu____784 = (

let uu____790 = (

let uu____792 = (

let uu____795 = (

let uu____801 = (

let uu____803 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____803)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____801))
in (FStar_Syntax_Util.mk_app c_pure uu____795))
in (

let uu____804 = (

let uu____808 = (FStar_Syntax_Syntax.bv_to_name a1)
in (uu____808)::[])
in (uu____792)::uu____804))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____790))
in (FStar_Syntax_Util.mk_app c_app uu____784))
in (

let uu____811 = (

let uu____815 = (FStar_Syntax_Syntax.bv_to_name a2)
in (uu____815)::[])
in (uu____781)::uu____811))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____779))
in (FStar_Syntax_Util.mk_app c_app uu____773))
in (FStar_Syntax_Util.abs uu____742 uu____772 ret)))))))))))
in (

let c_lift2 = (

let uu____819 = (mk_lid "lift2")
in (register env uu____819 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____826 = (

let uu____830 = (

let uu____831 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____831))
in (uu____830)::[])
in (

let uu____832 = (

let uu____835 = (

let uu____836 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx uu____836))
in (FStar_Syntax_Syntax.mk_Total uu____835))
in (FStar_Syntax_Util.arrow uu____826 uu____832)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (

let uu____845 = (

let uu____851 = (

let uu____852 = (

let uu____855 = (

let uu____856 = (

let uu____857 = (

let uu____861 = (

let uu____862 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder uu____862))
in (uu____861)::[])
in (

let uu____863 = (

let uu____866 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal uu____866))
in (FStar_Syntax_Util.arrow uu____857 uu____863)))
in (mk_ctx uu____856))
in (FStar_Syntax_Syntax.mk_Total uu____855))
in (FStar_Syntax_Util.lcomp_of_comp uu____852))
in FStar_Util.Inl (uu____851))
in Some (uu____845))
in (

let e1 = (

let uu____876 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None uu____876))
in (

let body = (

let uu____878 = (

let uu____882 = (

let uu____886 = (FStar_Syntax_Syntax.mk_binder e1)
in (uu____886)::[])
in (FStar_List.append gamma uu____882))
in (

let uu____889 = (

let uu____890 = (FStar_Syntax_Syntax.bv_to_name f)
in (

let uu____893 = (

let uu____899 = (

let uu____900 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg uu____900))
in (

let uu____901 = (args_of_binders gamma)
in (uu____899)::uu____901))
in (FStar_Syntax_Util.mk_app uu____890 uu____893)))
in (FStar_Syntax_Util.abs uu____878 uu____889 ret)))
in (

let uu____903 = (

let uu____907 = (mk_all_implicit binders)
in (

let uu____911 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append uu____907 uu____911)))
in (FStar_Syntax_Util.abs uu____903 body ret)))))))))
in (

let c_push = (

let uu____928 = (mk_lid "push")
in (register env uu____928 c_push))
in (

let ret_tot_wp_a = (

let uu____936 = (

let uu____942 = (

let uu____943 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp uu____943))
in FStar_Util.Inl (uu____942))
in Some (uu____936))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____971 = (

let uu____972 = (

let uu____982 = (args_of_binders binders)
in ((c), (uu____982)))
in FStar_Syntax_Syntax.Tm_app (uu____972))
in (mk uu____971))
end
| uu____987 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (

let uu____990 = (

let uu____991 = (

let uu____995 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____996 = (

let uu____998 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____998)::[])
in (uu____995)::uu____996))
in (

let uu____999 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____991 uu____999)))
in (FStar_Syntax_Syntax.mk_Total uu____990))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (

let uu____1003 = (

let uu____1007 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders uu____1007))
in (

let uu____1013 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (

let uu____1015 = (

let uu____1018 = (

let uu____1024 = (

let uu____1026 = (

let uu____1029 = (

let uu____1035 = (

let uu____1036 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg uu____1036))
in (uu____1035)::[])
in (FStar_Syntax_Util.mk_app l_ite uu____1029))
in (uu____1026)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1024))
in (FStar_Syntax_Util.mk_app c_lift2 uu____1018))
in (FStar_Syntax_Util.ascribe uu____1015 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs uu____1003 uu____1013 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (

let uu____1052 = (mk_lid "wp_if_then_else")
in (register env uu____1052 wp_if_then_else))
in (

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (

let uu____1063 = (

let uu____1069 = (

let uu____1071 = (

let uu____1074 = (

let uu____1080 = (

let uu____1082 = (

let uu____1085 = (

let uu____1091 = (

let uu____1092 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1092))
in (uu____1091)::[])
in (FStar_Syntax_Util.mk_app l_and uu____1085))
in (uu____1082)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1080))
in (FStar_Syntax_Util.mk_app c_pure uu____1074))
in (

let uu____1097 = (

let uu____1101 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1101)::[])
in (uu____1071)::uu____1097))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1069))
in (FStar_Syntax_Util.mk_app c_app uu____1063))
in (

let uu____1104 = (

let uu____1108 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1108))
in (FStar_Syntax_Util.abs uu____1104 body ret_tot_wp_a))))))
in (

let wp_assert = (

let uu____1115 = (mk_lid "wp_assert")
in (register env uu____1115 wp_assert))
in (

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (

let uu____1126 = (

let uu____1132 = (

let uu____1134 = (

let uu____1137 = (

let uu____1143 = (

let uu____1145 = (

let uu____1148 = (

let uu____1154 = (

let uu____1155 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg uu____1155))
in (uu____1154)::[])
in (FStar_Syntax_Util.mk_app l_imp uu____1148))
in (uu____1145)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1143))
in (FStar_Syntax_Util.mk_app c_pure uu____1137))
in (

let uu____1160 = (

let uu____1164 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____1164)::[])
in (uu____1134)::uu____1160))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1132))
in (FStar_Syntax_Util.mk_app c_app uu____1126))
in (

let uu____1167 = (

let uu____1171 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders uu____1171))
in (FStar_Syntax_Util.abs uu____1167 body ret_tot_wp_a))))))
in (

let wp_assume = (

let uu____1178 = (mk_lid "wp_assume")
in (register env uu____1178 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (

let uu____1187 = (

let uu____1191 = (

let uu____1192 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1192))
in (uu____1191)::[])
in (

let uu____1193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1187 uu____1193)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (

let uu____1200 = (

let uu____1206 = (

let uu____1208 = (

let uu____1211 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure uu____1211))
in (

let uu____1217 = (

let uu____1221 = (

let uu____1224 = (

let uu____1230 = (

let uu____1232 = (FStar_Syntax_Syntax.bv_to_name f)
in (uu____1232)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1230))
in (FStar_Syntax_Util.mk_app c_push uu____1224))
in (uu____1221)::[])
in (uu____1208)::uu____1217))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1206))
in (FStar_Syntax_Util.mk_app c_app uu____1200))
in (

let uu____1239 = (

let uu____1243 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders uu____1243))
in (FStar_Syntax_Util.abs uu____1239 body ret_tot_wp_a))))))
in (

let wp_close = (

let uu____1250 = (mk_lid "wp_close")
in (register env uu____1250 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (

let uu____1261 = (

let uu____1267 = (

let uu____1268 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____1268))
in FStar_Util.Inl (uu____1267))
in Some (uu____1261))
in (

let ret_gtot_type = (

let uu____1288 = (

let uu____1294 = (

let uu____1295 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____1295))
in FStar_Util.Inl (uu____1294))
in Some (uu____1288))
in (

let mk_forall = (fun x body -> (

let uu____1317 = (

let uu____1320 = (

let uu____1321 = (

let uu____1331 = (

let uu____1333 = (

let uu____1334 = (

let uu____1335 = (

let uu____1339 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1339)::[])
in (FStar_Syntax_Util.abs uu____1335 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg uu____1334))
in (uu____1333)::[])
in ((FStar_Syntax_Util.tforall), (uu____1331)))
in FStar_Syntax_Syntax.Tm_app (uu____1321))
in (FStar_Syntax_Syntax.mk uu____1320))
in (uu____1317 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (

let uu____1353 = (

let uu____1354 = (FStar_Syntax_Subst.compress t)
in uu____1354.FStar_Syntax_Syntax.n)
in (match (uu____1353) with
| FStar_Syntax_Syntax.Tm_type (uu____1357) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____1372 -> (match (uu____1372) with
| (b, uu____1376) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____1377 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____1382 = (

let uu____1383 = (FStar_Syntax_Subst.compress t)
in uu____1383.FStar_Syntax_Syntax.n)
in (match (uu____1382) with
| FStar_Syntax_Syntax.Tm_type (uu____1386) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____1401 -> (match (uu____1401) with
| (b, uu____1405) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____1406 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____1458 = (

let uu____1459 = (FStar_Syntax_Subst.compress t)
in uu____1459.FStar_Syntax_Syntax.n)
in (match (uu____1458) with
| FStar_Syntax_Syntax.Tm_type (uu____1462) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____1508 = ((is_monotonic a) || (is_monotonic b))
in (match (uu____1508) with
| true -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (

let uu____1511 = (

let uu____1514 = (

let uu____1520 = (

let uu____1521 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1521))
in (uu____1520)::[])
in (FStar_Syntax_Util.mk_app x uu____1514))
in (

let uu____1522 = (

let uu____1525 = (

let uu____1531 = (

let uu____1532 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1532))
in (uu____1531)::[])
in (FStar_Syntax_Util.mk_app y uu____1525))
in (mk_rel b uu____1511 uu____1522)))
in (mk_forall a1 body)))
end
| uu____1533 -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (

let uu____1537 = (

let uu____1538 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____1541 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a uu____1538 uu____1541)))
in (

let uu____1544 = (

let uu____1545 = (

let uu____1548 = (

let uu____1554 = (

let uu____1555 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg uu____1555))
in (uu____1554)::[])
in (FStar_Syntax_Util.mk_app x uu____1548))
in (

let uu____1556 = (

let uu____1559 = (

let uu____1565 = (

let uu____1566 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg uu____1566))
in (uu____1565)::[])
in (FStar_Syntax_Util.mk_app y uu____1559))
in (mk_rel b uu____1545 uu____1556)))
in (FStar_Syntax_Util.mk_imp uu____1537 uu____1544)))
in (

let uu____1567 = (mk_forall a2 body)
in (mk_forall a1 uu____1567)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let uu___94_1588 = t
in (

let uu____1589 = (

let uu____1590 = (

let uu____1598 = (

let uu____1599 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total uu____1599))
in (((binder)::[]), (uu____1598)))
in FStar_Syntax_Syntax.Tm_arrow (uu____1590))
in {FStar_Syntax_Syntax.n = uu____1589; FStar_Syntax_Syntax.tk = uu___94_1588.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___94_1588.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___94_1588.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1611) -> begin
(failwith "unhandled arrow")
end
| uu____1619 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end)))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let rec mk_stronger = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____1634 = (

let uu____1635 = (FStar_Syntax_Subst.compress t)
in uu____1635.FStar_Syntax_Syntax.n)
in (match (uu____1634) with
| FStar_Syntax_Syntax.Tm_type (uu____1638) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (

let uu____1655 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor uu____1655)) -> begin
(

let project = (fun i tuple -> (

let projector = (

let uu____1670 = (

let uu____1671 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env uu____1671 i))
in (FStar_Syntax_Syntax.fvar uu____1670 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let uu____1692 = (

let uu____1696 = (FStar_List.mapi (fun i uu____1701 -> (match (uu____1701) with
| (t, q) -> begin
(

let uu____1706 = (project i x)
in (

let uu____1707 = (project i y)
in (mk_stronger t uu____1706 uu____1707)))
end)) args)
in (match (uu____1696) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____1692) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____1763 -> (match (uu____1763) with
| (bv, q) -> begin
(

let uu____1768 = (

let uu____1769 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" uu____1769))
in (FStar_Syntax_Syntax.gen_bv uu____1768 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (

let uu____1773 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg uu____1773))) bvs)
in (

let body = (

let uu____1775 = (FStar_Syntax_Util.mk_app x args)
in (

let uu____1776 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b uu____1775 uu____1776)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| uu____1779 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (

let uu____1781 = (FStar_Syntax_Util.unascribe wp_a)
in (

let uu____1782 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (

let uu____1783 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger uu____1781 uu____1782 uu____1783))))
in (

let uu____1784 = (

let uu____1788 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders uu____1788))
in (FStar_Syntax_Util.abs uu____1784 body ret_tot_type))))))
in (

let stronger = (

let uu____1803 = (mk_lid "stronger")
in (register env uu____1803 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1809 = (FStar_Util.prefix gamma)
in (match (uu____1809) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (

let uu____1835 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm uu____1835))
in (

let uu____1838 = (FStar_Syntax_Util.destruct_typ_as_formula eq)
in (match (uu____1838) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (

let uu____1846 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm uu____1846))
in (

let guard_free = (

let uu____1853 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1853))
in (

let pat = (

let uu____1857 = (

let uu____1863 = (FStar_Syntax_Syntax.as_arg k_app)
in (uu____1863)::[])
in (FStar_Syntax_Util.mk_app guard_free uu____1857))
in (

let pattern_guarded_body = (

let uu____1867 = (

let uu____1868 = (

let uu____1873 = (

let uu____1874 = (

let uu____1881 = (

let uu____1883 = (FStar_Syntax_Syntax.as_arg pat)
in (uu____1883)::[])
in (uu____1881)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____1874))
in ((body), (uu____1873)))
in FStar_Syntax_Syntax.Tm_meta (uu____1868))
in (mk uu____1867))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| uu____1886 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (

let uu____1889 = (

let uu____1890 = (

let uu____1891 = (

let uu____1892 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1895 = (

let uu____1901 = (args_of_binders wp_args)
in (

let uu____1903 = (

let uu____1905 = (

let uu____1906 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg uu____1906))
in (uu____1905)::[])
in (FStar_List.append uu____1901 uu____1903)))
in (FStar_Syntax_Util.mk_app uu____1892 uu____1895)))
in (FStar_Syntax_Util.mk_imp equiv uu____1891))
in (FStar_Syntax_Util.mk_forall k uu____1890))
in (FStar_Syntax_Util.abs gamma uu____1889 ret_gtot_type))
in (

let uu____1907 = (

let uu____1911 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders uu____1911))
in (FStar_Syntax_Util.abs uu____1907 body ret_gtot_type)))))
end)))
in (

let wp_ite = (

let uu____1918 = (mk_lid "wp_ite")
in (register env uu____1918 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1924 = (FStar_Util.prefix gamma)
in (match (uu____1924) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (

let uu____1950 = (

let uu____1951 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (

let uu____1954 = (

let uu____1960 = (

let uu____1961 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____1961))
in (uu____1960)::[])
in (FStar_Syntax_Util.mk_app uu____1951 uu____1954)))
in (FStar_Syntax_Util.mk_forall x uu____1950))
in (

let uu____1962 = (

let uu____1966 = (

let uu____1970 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append uu____1970 gamma))
in (FStar_List.append binders uu____1966))
in (FStar_Syntax_Util.abs uu____1962 body ret_gtot_type))))
end)))
in (

let null_wp = (

let uu____1979 = (mk_lid "null_wp")
in (register env uu____1979 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (

let uu____1988 = (

let uu____1994 = (

let uu____1996 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1997 = (

let uu____1999 = (

let uu____2002 = (

let uu____2008 = (

let uu____2009 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg uu____2009))
in (uu____2008)::[])
in (FStar_Syntax_Util.mk_app null_wp uu____2002))
in (

let uu____2010 = (

let uu____2014 = (FStar_Syntax_Syntax.bv_to_name wp)
in (uu____2014)::[])
in (uu____1999)::uu____2010))
in (uu____1996)::uu____1997))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1994))
in (FStar_Syntax_Util.mk_app stronger uu____1988))
in (

let uu____2017 = (

let uu____2021 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders uu____2021))
in (FStar_Syntax_Util.abs uu____2017 body ret_tot_type))))
in (

let wp_trivial = (

let uu____2028 = (mk_lid "wp_trivial")
in (register env uu____2028 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in ((

let uu____2033 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____2033) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____2034 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (

let uu____2038 = (

let uu____2040 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2040))
in (

let uu____2045 = (

let uu___95_2046 = ed
in (

let uu____2047 = (

let uu____2048 = (c wp_if_then_else)
in (([]), (uu____2048)))
in (

let uu____2050 = (

let uu____2051 = (c wp_ite)
in (([]), (uu____2051)))
in (

let uu____2053 = (

let uu____2054 = (c stronger)
in (([]), (uu____2054)))
in (

let uu____2056 = (

let uu____2057 = (c wp_close)
in (([]), (uu____2057)))
in (

let uu____2059 = (

let uu____2060 = (c wp_assert)
in (([]), (uu____2060)))
in (

let uu____2062 = (

let uu____2063 = (c wp_assume)
in (([]), (uu____2063)))
in (

let uu____2065 = (

let uu____2066 = (c null_wp)
in (([]), (uu____2066)))
in (

let uu____2068 = (

let uu____2069 = (c wp_trivial)
in (([]), (uu____2069)))
in {FStar_Syntax_Syntax.qualifiers = uu___95_2046.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___95_2046.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___95_2046.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___95_2046.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___95_2046.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___95_2046.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___95_2046.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___95_2046.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu____2047; FStar_Syntax_Syntax.ite_wp = uu____2050; FStar_Syntax_Syntax.stronger = uu____2053; FStar_Syntax_Syntax.close_wp = uu____2056; FStar_Syntax_Syntax.assert_p = uu____2059; FStar_Syntax_Syntax.assume_p = uu____2062; FStar_Syntax_Syntax.null_wp = uu____2065; FStar_Syntax_Syntax.trivial = uu____2068; FStar_Syntax_Syntax.repr = uu___95_2046.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___95_2046.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___95_2046.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___95_2046.FStar_Syntax_Syntax.actions})))))))))
in ((uu____2038), (uu____2045)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____2085 -> begin
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
| uu____2097 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun uu___82_2107 -> (match (uu___82_2107) with
| FStar_Syntax_Syntax.Total (t, uu____2109) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___81_2118 -> (match (uu___81_2118) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2119 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let uu____2121 = (

let uu____2122 = (

let uu____2123 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2123))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2122))
in (failwith uu____2121))
end
| FStar_Syntax_Syntax.GTotal (uu____2124) -> begin
(failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___83_2132 -> (match (uu___83_2132) with
| N (t) -> begin
(

let uu____2134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" uu____2134))
end
| M (t) -> begin
(

let uu____2136 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" uu____2136))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2140, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = uu____2142; FStar_Syntax_Syntax.pos = uu____2143; FStar_Syntax_Syntax.vars = uu____2144}) -> begin
(nm_of_comp n)
end
| uu____2155 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (

let uu____2167 = (nm_of_comp c.FStar_Syntax_Syntax.n)
in (match (uu____2167) with
| M (uu____2168) -> begin
true
end
| N (uu____2169) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____2173 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ -> (

let uu____2183 = (

let uu____2187 = (

let uu____2188 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2188))
in (uu____2187)::[])
in (

let uu____2189 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____2183 uu____2189))))
in (

let uu____2192 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once uu____2192))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (mk (

let uu____2227 = (

let uu____2235 = (

let uu____2239 = (

let uu____2242 = (

let uu____2243 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv uu____2243))
in (

let uu____2244 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2242), (uu____2244))))
in (uu____2239)::[])
in (

let uu____2249 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____2235), (uu____2249))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2227))))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____2282) -> begin
(

let binders = (FStar_List.map (fun uu____2301 -> (match (uu____2301) with
| (bv, aqual) -> begin
(

let uu____2308 = (

let uu___96_2309 = bv
in (

let uu____2310 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___96_2309.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___96_2309.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2310}))
in ((uu____2308), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2313, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____2315); FStar_Syntax_Syntax.tk = uu____2316; FStar_Syntax_Syntax.pos = uu____2317; FStar_Syntax_Syntax.vars = uu____2318}) -> begin
(

let uu____2335 = (

let uu____2336 = (

let uu____2344 = (

let uu____2345 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal uu____2345))
in ((binders), (uu____2344)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2336))
in (mk uu____2335))
end
| uu____2349 -> begin
(

let uu____2350 = (is_monadic_arrow t.FStar_Syntax_Syntax.n)
in (match (uu____2350) with
| N (hn) -> begin
(

let uu____2352 = (

let uu____2353 = (

let uu____2361 = (

let uu____2362 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total uu____2362))
in ((binders), (uu____2361)))
in FStar_Syntax_Syntax.Tm_arrow (uu____2353))
in (mk uu____2352))
end
| M (a) -> begin
(

let uu____2367 = (

let uu____2368 = (

let uu____2376 = (

let uu____2380 = (

let uu____2384 = (

let uu____2387 = (

let uu____2388 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv uu____2388))
in (

let uu____2389 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2387), (uu____2389))))
in (uu____2384)::[])
in (FStar_List.append binders uu____2380))
in (

let uu____2396 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((uu____2376), (uu____2396))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2368))
in (mk uu____2367))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let debug = (fun t s -> (

let string_of_set = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(

let uu____2447 = (f x)
in (FStar_Util.string_builder_append strb uu____2447));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2451 = (f x)
in (FStar_Util.string_builder_append strb uu____2451));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (

let uu____2453 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2454 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" uu____2453 uu____2454)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (

let uu____2462 = (

let uu____2463 = (FStar_Syntax_Subst.compress ty)
in uu____2463.FStar_Syntax_Syntax.n)
in (match (uu____2462) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2478 = (

let uu____2479 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (not (uu____2479)))
in (match (uu____2478) with
| true -> begin
false
end
| uu____2480 -> begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (

let uu____2493 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect uu____2493 s))
in (

let uu____2495 = (

let uu____2496 = (FStar_Util.set_is_empty sinter)
in (not (uu____2496)))
in (match (uu____2495) with
| true -> begin
((debug ty sinter);
(Prims.raise Not_found);
)
end
| uu____2498 -> begin
()
end))))
in (

let uu____2499 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2499) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s uu____2510 -> (match (uu____2510) with
| (bv, uu____2516) -> begin
((non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort);
(FStar_Util.set_add bv s);
)
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in ((non_dependent_or_raise s ct);
(

let k = (n - (FStar_List.length binders))
in (match ((k > (Prims.parse_int "0"))) with
| true -> begin
(is_non_dependent_arrow ct k)
end
| uu____2527 -> begin
true
end));
)))
end)))
end)
with
| Not_found -> begin
false
end
end))
end
| uu____2529 -> begin
((

let uu____2531 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" uu____2531));
false;
)
end)))
in (

let rec is_valid_application = (fun head -> (

let uu____2536 = (

let uu____2537 = (FStar_Syntax_Subst.compress head)
in uu____2537.FStar_Syntax_Syntax.n)
in (match (uu____2536) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (

let uu____2541 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor uu____2541))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____2554) -> begin
true
end
| uu____2564 -> begin
((

let uu____2566 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" uu____2566));
false;
)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2570) -> begin
(is_valid_application t)
end
| uu____2575 -> begin
false
end)))
in (

let uu____2576 = (is_valid_application head)
in (match (uu____2576) with
| true -> begin
(

let uu____2577 = (

let uu____2578 = (

let uu____2588 = (FStar_List.map (fun uu____2598 -> (match (uu____2598) with
| (t, qual) -> begin
(

let uu____2611 = (star_type' env t)
in ((uu____2611), (qual)))
end)) args)
in ((head), (uu____2588)))
in FStar_Syntax_Syntax.Tm_app (uu____2578))
in (mk uu____2577))
end
| uu____2617 -> begin
(

let uu____2618 = (

let uu____2619 = (

let uu____2620 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" uu____2620))
in FStar_Errors.Err (uu____2619))
in (Prims.raise uu____2618))
end)))))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____2650 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____2650) with
| (binders, repr) -> begin
(

let env = (

let uu___99_2656 = env
in (

let uu____2657 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = uu____2657; subst = uu___99_2656.subst; tc_const = uu___99_2656.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, t) when false -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv x)
in (

let sort = (star_type' env x.FStar_Syntax_Syntax.sort)
in (

let subst = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let t = (star_type' env t)
in (

let subst = (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___100_2674 = x
in {FStar_Syntax_Syntax.ppname = uu___100_2674.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_2674.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(

let uu____2681 = (

let uu____2682 = (

let uu____2687 = (star_type' env t)
in ((uu____2687), (m)))
in FStar_Syntax_Syntax.Tm_meta (uu____2682))
in (mk uu____2681))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(

let uu____2709 = (

let uu____2710 = (

let uu____2723 = (star_type' env e)
in (

let uu____2724 = (

let uu____2729 = (star_type' env t)
in FStar_Util.Inl (uu____2729))
in ((uu____2723), (uu____2724), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____2710))
in (mk uu____2709))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2737) -> begin
(

let uu____2750 = (

let uu____2751 = (

let uu____2752 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" uu____2752))
in FStar_Errors.Err (uu____2751))
in (Prims.raise uu____2750))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2753) -> begin
(

let uu____2758 = (

let uu____2759 = (

let uu____2760 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" uu____2760))
in FStar_Errors.Err (uu____2759))
in (Prims.raise uu____2758))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2761) -> begin
(

let uu____2766 = (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" uu____2768))
in FStar_Errors.Err (uu____2767))
in (Prims.raise uu____2766))
end
| FStar_Syntax_Syntax.Tm_constant (uu____2769) -> begin
(

let uu____2770 = (

let uu____2771 = (

let uu____2772 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" uu____2772))
in FStar_Errors.Err (uu____2771))
in (Prims.raise uu____2770))
end
| FStar_Syntax_Syntax.Tm_match (uu____2773) -> begin
(

let uu____2789 = (

let uu____2790 = (

let uu____2791 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" uu____2791))
in FStar_Errors.Err (uu____2790))
in (Prims.raise uu____2789))
end
| FStar_Syntax_Syntax.Tm_let (uu____2792) -> begin
(

let uu____2800 = (

let uu____2801 = (

let uu____2802 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" uu____2802))
in FStar_Errors.Err (uu____2801))
in (Prims.raise uu____2800))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2803) -> begin
(

let uu____2812 = (

let uu____2813 = (

let uu____2814 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" uu____2814))
in FStar_Errors.Err (uu____2813))
in (Prims.raise uu____2812))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____2815 = (

let uu____2816 = (

let uu____2817 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" uu____2817))
in FStar_Errors.Err (uu____2816))
in (Prims.raise uu____2815))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2818) -> begin
(failwith "impossible")
end)))))


let is_monadic = (fun uu___85_2851 -> (match (uu___85_2851) with
| None -> begin
(failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (_, flags))) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___84_2888 -> (match (uu___84_2888) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2889 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____2893 = (

let uu____2894 = (FStar_Syntax_Subst.compress t)
in uu____2894.FStar_Syntax_Syntax.n)
in (match (uu____2893) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (

let uu____2914 = (

let uu____2915 = (FStar_List.hd args)
in (Prims.fst uu____2915))
in (is_C uu____2914))
in (match (r) with
| true -> begin
((

let uu____2927 = (

let uu____2928 = (FStar_List.for_all (fun uu____2931 -> (match (uu____2931) with
| (h, uu____2935) -> begin
(is_C h)
end)) args)
in (not (uu____2928)))
in (match (uu____2927) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____2936 -> begin
()
end));
true;
)
end
| uu____2937 -> begin
((

let uu____2939 = (

let uu____2940 = (FStar_List.for_all (fun uu____2943 -> (match (uu____2943) with
| (h, uu____2947) -> begin
(

let uu____2948 = (is_C h)
in (not (uu____2948)))
end)) args)
in (not (uu____2940)))
in (match (uu____2939) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____2949 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____2962 = (nm_of_comp comp.FStar_Syntax_Syntax.n)
in (match (uu____2962) with
| M (t) -> begin
((

let uu____2965 = (is_C t)
in (match (uu____2965) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____2966 -> begin
()
end));
true;
)
end
| N (t) -> begin
(is_C t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_C t)
end
| uu____2992 -> begin
false
end)))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (

let uu____3023 = (

let uu____3024 = (

let uu____3034 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____3035 = (

let uu____3039 = (

let uu____3042 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (uu____3042)))
in (uu____3039)::[])
in ((uu____3034), (uu____3035))))
in FStar_Syntax_Syntax.Tm_app (uu____3024))
in (mk uu____3023))
in (

let uu____3050 = (

let uu____3054 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____3054)::[])
in (FStar_Syntax_Util.abs uu____3050 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___86_3062 -> (match (uu___86_3062) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____3063 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun uu____3207 -> (match (uu____3207) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> (

let uu____3228 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (

let uu____3229 = (

let uu____3230 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial uu____3230))
in (not (uu____3229))))
in (match (uu____3228) with
| true -> begin
(

let uu____3231 = (

let uu____3232 = (

let uu____3233 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3234 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____3235 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" uu____3233 uu____3234 uu____3235))))
in FStar_Errors.Err (uu____3232))
in (Prims.raise uu____3231))
end
| uu____3236 -> begin
()
end)))
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
((check t1 t2);
((rec_nm), (s_e), (u_e));
)
end
| (N (t1), M (t2)) -> begin
((check t1 t2);
(

let uu____3246 = (mk_return env t1 s_e)
in ((M (t1)), (uu____3246), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(

let uu____3249 = (

let uu____3250 = (

let uu____3251 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____3252 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____3253 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" uu____3251 uu____3252 uu____3253))))
in FStar_Errors.Err (uu____3250))
in (Prims.raise uu____3249))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun uu___87_3279 -> (match (uu___87_3279) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____3289 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(

let uu____3300 = (

let uu____3301 = (

let uu____3304 = (

let uu____3305 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " uu____3305))
in ((uu____3304), (e2.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____3301))
in (Prims.raise uu____3300))
end
| M (uu____3309) -> begin
(

let uu____3310 = (check env e2 context_nm)
in (strip_m uu____3310))
end)))
in (

let uu____3314 = (

let uu____3315 = (FStar_Syntax_Subst.compress e)
in uu____3315.FStar_Syntax_Syntax.n)
in (match (uu____3314) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(

let uu____3327 = (infer env e)
in (return_if uu____3327))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____3397) -> begin
(

let uu____3405 = (

let uu____3406 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" uu____3406))
in (failwith uu____3405))
end
| FStar_Syntax_Syntax.Tm_type (uu____3410) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3414) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____3425) -> begin
(

let uu____3430 = (

let uu____3431 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" uu____3431))
in (failwith uu____3430))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3435) -> begin
(

let uu____3444 = (

let uu____3445 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" uu____3445))
in (failwith uu____3444))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3449) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3473 = (

let uu____3474 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" uu____3474))
in (failwith uu____3473))
end))))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (

let uu____3496 = (

let uu____3497 = (FStar_Syntax_Subst.compress e)
in uu____3497.FStar_Syntax_Syntax.n)
in (match (uu____3496) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let body = (FStar_Syntax_Subst.subst subst body)
in (

let env = (

let uu___101_3537 = env
in (

let uu____3538 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = uu____3538; subst = uu___101_3537.subst; tc_const = uu___101_3537.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____3547 -> (match (uu____3547) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let uu___102_3555 = bv
in {FStar_Syntax_Syntax.ppname = uu___102_3555.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_3555.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let uu____3556 = (FStar_List.fold_left (fun uu____3565 uu____3566 -> (match (((uu____3565), (uu____3566))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____3594 = (is_C c)
in (match (uu____3594) with
| true -> begin
(

let xw = (

let uu____3599 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None uu____3599))
in (

let x = (

let uu___103_3601 = bv
in (

let uu____3602 = (

let uu____3605 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c uu____3605))
in {FStar_Syntax_Syntax.ppname = uu___103_3601.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_3601.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3602}))
in (

let env = (

let uu___104_3607 = env
in (

let uu____3608 = (

let uu____3610 = (

let uu____3611 = (

let uu____3616 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (uu____3616)))
in FStar_Syntax_Syntax.NT (uu____3611))
in (uu____3610)::env.subst)
in {env = uu___104_3607.env; subst = uu____3608; tc_const = uu___104_3607.tc_const}))
in (

let uu____3617 = (

let uu____3619 = (FStar_Syntax_Syntax.mk_binder x)
in (

let uu____3620 = (

let uu____3622 = (FStar_Syntax_Syntax.mk_binder xw)
in (uu____3622)::acc)
in (uu____3619)::uu____3620))
in ((env), (uu____3617))))))
end
| uu____3624 -> begin
(

let x = (

let uu___105_3626 = bv
in (

let uu____3627 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_3626.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_3626.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3627}))
in (

let uu____3630 = (

let uu____3632 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3632)::acc)
in ((env), (uu____3630))))
end)))
end)) ((env), ([])) binders)
in (match (uu____3556) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let uu____3644 = (

let check_what = (

let uu____3656 = (is_monadic what)
in (match (uu____3656) with
| true -> begin
check_m
end
| uu____3664 -> begin
check_n
end))
in (

let uu____3665 = (check_what env body)
in (match (uu____3665) with
| (t, s_body, u_body) -> begin
(

let uu____3675 = (

let uu____3676 = (

let uu____3677 = (is_monadic what)
in (match (uu____3677) with
| true -> begin
M (t)
end
| uu____3678 -> begin
N (t)
end))
in (comp_of_nm uu____3676))
in ((uu____3675), (s_body), (u_body)))
end)))
in (match (uu____3644) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____3720 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___88_3722 -> (match (uu___88_3722) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____3723 -> begin
false
end))))
in (match (uu____3720) with
| true -> begin
(

let double_starred_comp = (

let uu____3731 = (

let uu____3732 = (

let uu____3733 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result uu____3733))
in (FStar_All.pipe_left double_star uu____3732))
in (FStar_Syntax_Syntax.mk_Total uu____3731))
in (

let flags = (FStar_List.filter (fun uu___89_3738 -> (match (uu___89_3738) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____3739 -> begin
true
end)) lc.FStar_Syntax_Syntax.cflags)
in (

let uu____3740 = (

let uu____3746 = (

let uu____3747 = (FStar_Syntax_Util.comp_set_flags double_starred_comp flags)
in (FStar_Syntax_Util.lcomp_of_comp uu____3747))
in FStar_Util.Inl (uu____3746))
in Some (uu____3740))))
end
| uu____3758 -> begin
Some (FStar_Util.Inl ((

let uu___106_3767 = lc
in {FStar_Syntax_Syntax.eff_name = uu___106_3767.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___106_3767.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___106_3767.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____3768 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ))))})))
end))
end
| Some (FStar_Util.Inr (lid, flags)) -> begin
(

let uu____3785 = (

let uu____3791 = (

let uu____3795 = (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___90_3797 -> (match (uu___90_3797) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____3798 -> begin
false
end))))
in (match (uu____3795) with
| true -> begin
(

let uu____3802 = (FStar_List.filter (fun uu___91_3804 -> (match (uu___91_3804) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____3805 -> begin
true
end)) flags)
in ((FStar_Syntax_Const.effect_Tot_lid), (uu____3802)))
end
| uu____3807 -> begin
((lid), (flags))
end))
in FStar_Util.Inr (uu____3791))
in Some (uu____3785))
end)
in (

let uu____3817 = (

let comp = (

let uu____3829 = (is_monadic what)
in (

let uu____3830 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) uu____3829 uu____3830)))
in (

let uu____3831 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((uu____3831), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (uu____3817) with
| (u_body, u_what) -> begin
(

let s_body = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (mk (FStar_Syntax_Syntax.Tm_abs (((s_binders), (s_body), (s_what)))))
in (

let u_body = (FStar_Syntax_Subst.close u_binders u_body)
in (

let u_binders = (FStar_Syntax_Subst.close_binders u_binders)
in (

let u_term = (mk (FStar_Syntax_Syntax.Tm_abs (((u_binders), (u_body), (u_what)))))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = uu____3900; FStar_Syntax_Syntax.p = uu____3901}; FStar_Syntax_Syntax.fv_delta = uu____3902; FStar_Syntax_Syntax.fv_qual = uu____3903}) -> begin
(

let uu____3909 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (uu____3909) with
| (uu____3915, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let uu____3918 = (

let uu____3919 = (normalize t)
in N (uu____3919))
in ((uu____3918), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____3936 = (check_n env head)
in (match (uu____3936) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____3950 = (

let uu____3951 = (FStar_Syntax_Subst.compress t)
in uu____3951.FStar_Syntax_Syntax.n)
in (match (uu____3950) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3954) -> begin
true
end
| uu____3962 -> begin
false
end)))
in (

let rec flatten = (fun t -> (

let uu____3974 = (

let uu____3975 = (FStar_Syntax_Subst.compress t)
in uu____3975.FStar_Syntax_Syntax.n)
in (match (uu____3974) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, uu____3987); FStar_Syntax_Syntax.tk = uu____3988; FStar_Syntax_Syntax.pos = uu____3989; FStar_Syntax_Syntax.vars = uu____3990}) when (is_arrow t) -> begin
(

let uu____4007 = (flatten t)
in (match (uu____4007) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____4059, uu____4060) -> begin
(flatten e)
end
| uu____4079 -> begin
(

let uu____4080 = (

let uu____4081 = (

let uu____4082 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" uu____4082))
in FStar_Errors.Err (uu____4081))
in (Prims.raise uu____4080))
end)))
in (

let uu____4090 = (flatten t_head)
in (match (uu____4090) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(

let uu____4135 = (

let uu____4136 = (

let uu____4137 = (FStar_Util.string_of_int n)
in (

let uu____4141 = (FStar_Util.string_of_int (n' - n))
in (

let uu____4147 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." uu____4137 uu____4141 uu____4147))))
in FStar_Errors.Err (uu____4136))
in (Prims.raise uu____4135))
end
| uu____4151 -> begin
()
end);
(

let uu____4152 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____4152) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst uu____4179 args -> (match (uu____4179) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(

let uu____4222 = (

let uu____4223 = (FStar_Syntax_Subst.subst_comp subst comp)
in uu____4223.FStar_Syntax_Syntax.n)
in (nm_of_comp uu____4222))
end
| (binders, []) -> begin
(

let uu____4242 = (

let uu____4243 = (

let uu____4246 = (

let uu____4247 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst uu____4247))
in (FStar_Syntax_Subst.compress uu____4246))
in uu____4243.FStar_Syntax_Syntax.n)
in (match (uu____4242) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____4263 = (

let uu____4264 = (

let uu____4265 = (

let uu____4273 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (uu____4273)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4265))
in (mk uu____4264))
in N (uu____4263))
end
| uu____4277 -> begin
(failwith "wat?")
end))
end
| ([], (uu____4278)::uu____4279) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____4304))::binders, ((arg, uu____4307))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let uu____4341 = (FStar_List.splitAt n' binders)
in (match (uu____4341) with
| (binders, uu____4358) -> begin
(

let uu____4371 = (

let uu____4381 = (FStar_List.map2 (fun uu____4401 uu____4402 -> (match (((uu____4401), (uu____4402))) with
| ((bv, uu____4419), (arg, q)) -> begin
(

let uu____4426 = (

let uu____4427 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in uu____4427.FStar_Syntax_Syntax.n)
in (match (uu____4426) with
| FStar_Syntax_Syntax.Tm_type (uu____4437) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| uu____4450 -> begin
(

let uu____4451 = (check_n env arg)
in (match (uu____4451) with
| (uu____4462, s_arg, u_arg) -> begin
(

let uu____4465 = (

let uu____4469 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____4469) with
| true -> begin
(

let uu____4473 = (

let uu____4476 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((uu____4476), (q)))
in (uu____4473)::(((u_arg), (q)))::[])
end
| uu____4483 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (uu____4465)))
end))
end))
end)) binders args)
in (FStar_List.split uu____4381))
in (match (uu____4371) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (

let uu____4523 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (

let uu____4529 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (uu____4523), (uu____4529)))))
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
| (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(infer env e)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____4602 = (

let uu____4603 = (env.tc_const c)
in N (uu____4603))
in ((uu____4602), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (uu____4604) -> begin
(

let uu____4612 = (

let uu____4613 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" uu____4613))
in (failwith uu____4612))
end
| FStar_Syntax_Syntax.Tm_type (uu____4617) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____4621) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____4632) -> begin
(

let uu____4637 = (

let uu____4638 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" uu____4638))
in (failwith uu____4637))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____4642) -> begin
(

let uu____4651 = (

let uu____4652 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4652))
in (failwith uu____4651))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____4656) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____4680 = (

let uu____4681 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4681))
in (failwith uu____4680))
end)))))
and mk_match : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let uu____4719 = (check_n env e0)
in (match (uu____4719) with
| (uu____4726, s_e0, u_e0) -> begin
(

let uu____4729 = (

let uu____4747 = (FStar_List.map (fun b -> (

let uu____4780 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4780) with
| (pat, None, body) -> begin
(

let env = (

let uu___107_4812 = env
in (

let uu____4813 = (

let uu____4814 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env uu____4814))
in {env = uu____4813; subst = uu___107_4812.subst; tc_const = uu___107_4812.tc_const}))
in (

let uu____4816 = (f env body)
in (match (uu____4816) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| uu____4865 -> begin
(Prims.raise (FStar_Errors.Err ("No when clauses in the definition language")))
end))) branches)
in (FStar_List.split uu____4747))
in (match (uu____4729) with
| (nms, branches) -> begin
(

let t1 = (

let uu____4930 = (FStar_List.hd nms)
in (match (uu____4930) with
| (M (t1)) | (N (t1)) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___92_4933 -> (match (uu___92_4933) with
| M (uu____4934) -> begin
true
end
| uu____4935 -> begin
false
end)) nms)
in (

let uu____4936 = (

let uu____4959 = (FStar_List.map2 (fun nm uu____5011 -> (match (uu____5011) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let uu____5107 = (check env original_body (M (t2)))
in (match (uu____5107) with
| (uu____5130, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (uu____5159), false) -> begin
(failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 uu____4959))
in (match (uu____4936) with
| (nms, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun uu____5278 -> (match (uu____5278) with
| (pat, guard, s_body) -> begin
(

let s_body = (

let uu____5319 = (

let uu____5320 = (

let uu____5330 = (

let uu____5334 = (

let uu____5337 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5338 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5337), (uu____5338))))
in (uu____5334)::[])
in ((s_body), (uu____5330)))
in FStar_Syntax_Syntax.Tm_app (uu____5320))
in (mk uu____5319))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (

let uu____5360 = (

let uu____5364 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____5364)::[])
in (

let uu____5365 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs uu____5360 uu____5365 None)))
in (

let t1_star = (

let uu____5375 = (

let uu____5379 = (

let uu____5380 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____5380))
in (uu____5379)::[])
in (

let uu____5381 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow uu____5375 uu____5381)))
in (

let uu____5384 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (

let uu____5398 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (uu____5384), (uu____5398)))))))))))
end
| uu____5406 -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (

let uu____5412 = (

let uu____5415 = (

let uu____5416 = (

let uu____5429 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((uu____5429), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____5416))
in (mk uu____5415))
in (

let uu____5442 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (uu____5412), (uu____5442)))))))
end)
end))))
end))
end))))
and mk_let : env_  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.term  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env binding e2 proceed ensure_m -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos))
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (

let uu____5485 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5485)::[])
in (

let uu____5486 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____5486) with
| (x_binders, e2) -> begin
(

let uu____5494 = (infer env e1)
in (match (uu____5494) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____5505 = (is_C t1)
in (match (uu____5505) with
| true -> begin
(

let uu___108_5506 = binding
in (

let uu____5507 = (

let uu____5510 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 uu____5510))
in {FStar_Syntax_Syntax.lbname = uu___108_5506.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___108_5506.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5507; FStar_Syntax_Syntax.lbeff = uu___108_5506.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___108_5506.FStar_Syntax_Syntax.lbdef}))
end
| uu____5511 -> begin
binding
end))
in (

let env = (

let uu___109_5513 = env
in (

let uu____5514 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___110_5515 = x
in {FStar_Syntax_Syntax.ppname = uu___110_5515.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_5515.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____5514; subst = uu___109_5513.subst; tc_const = uu___109_5513.tc_const}))
in (

let uu____5516 = (proceed env e2)
in (match (uu____5516) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___111_5527 = binding
in (

let uu____5528 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___111_5527.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___111_5527.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____5528; FStar_Syntax_Syntax.lbeff = uu___111_5527.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___111_5527.FStar_Syntax_Syntax.lbdef}))
in (

let uu____5531 = (

let uu____5534 = (

let uu____5535 = (

let uu____5543 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let uu___112_5548 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___112_5548.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___112_5548.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___112_5548.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___112_5548.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (uu____5543)))
in FStar_Syntax_Syntax.Tm_let (uu____5535))
in (mk uu____5534))
in (

let uu____5549 = (

let uu____5552 = (

let uu____5553 = (

let uu____5561 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___113_5566 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___113_5566.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___113_5566.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___113_5566.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___113_5566.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (uu____5561)))
in FStar_Syntax_Syntax.Tm_let (uu____5553))
in (mk uu____5552))
in ((nm_rec), (uu____5531), (uu____5549)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___114_5575 = binding
in {FStar_Syntax_Syntax.lbname = uu___114_5575.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___114_5575.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___114_5575.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let uu___115_5577 = env
in (

let uu____5578 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___116_5579 = x
in {FStar_Syntax_Syntax.ppname = uu___116_5579.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_5579.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = uu____5578; subst = uu___115_5577.subst; tc_const = uu___115_5577.tc_const}))
in (

let uu____5580 = (ensure_m env e2)
in (match (uu____5580) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (

let uu____5597 = (

let uu____5598 = (

let uu____5608 = (

let uu____5612 = (

let uu____5615 = (FStar_Syntax_Syntax.bv_to_name p)
in (

let uu____5616 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5615), (uu____5616))))
in (uu____5612)::[])
in ((s_e2), (uu____5608)))
in FStar_Syntax_Syntax.Tm_app (uu____5598))
in (mk uu____5597))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (

let uu____5633 = (

let uu____5634 = (

let uu____5644 = (

let uu____5648 = (

let uu____5651 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (uu____5651)))
in (uu____5648)::[])
in ((s_e1), (uu____5644)))
in FStar_Syntax_Syntax.Tm_app (uu____5634))
in (mk uu____5633))
in (

let uu____5659 = (

let uu____5660 = (

let uu____5664 = (FStar_Syntax_Syntax.mk_binder p)
in (uu____5664)::[])
in (FStar_Syntax_Util.abs uu____5660 body None))
in (

let uu____5670 = (

let uu____5673 = (

let uu____5674 = (

let uu____5682 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___117_5687 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___117_5687.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_5687.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_5687.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_5687.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (uu____5682)))
in FStar_Syntax_Syntax.Tm_let (uu____5674))
in (mk uu____5673))
in ((M (t2)), (uu____5659), (uu____5670)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____5696 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (uu____5696))
in (

let uu____5701 = (check env e mn)
in (match (uu____5701) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____5711 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (

let uu____5724 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (uu____5724))
in (

let uu____5729 = (check env e mn)
in (match (uu____5729) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____5739 -> begin
(failwith "[check_m]: impossible")
end))))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> ((

let uu____5761 = (

let uu____5762 = (is_C c)
in (not (uu____5762)))
in (match (uu____5761) with
| true -> begin
(failwith "not a C")
end
| uu____5763 -> begin
()
end));
(

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (

let uu____5774 = (

let uu____5775 = (FStar_Syntax_Subst.compress c)
in uu____5775.FStar_Syntax_Syntax.n)
in (match (uu____5774) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____5794 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____5794) with
| (wp_head, wp_args) -> begin
((

let uu____5821 = ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (

let uu____5834 = (

let uu____5835 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head uu____5835))
in (not (uu____5834))))
in (match (uu____5821) with
| true -> begin
(failwith "mismatch")
end
| uu____5843 -> begin
()
end));
(

let uu____5844 = (

let uu____5845 = (

let uu____5855 = (FStar_List.map2 (fun uu____5865 uu____5866 -> (match (((uu____5865), (uu____5866))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> (

let uu____5889 = (FStar_Syntax_Syntax.is_implicit q)
in (match (uu____5889) with
| true -> begin
"implicit"
end
| uu____5890 -> begin
"explicit"
end)))
in ((match ((q <> q')) with
| true -> begin
(

let uu____5892 = (print_implicit q)
in (

let uu____5893 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" uu____5892 uu____5893)))
end
| uu____5894 -> begin
()
end);
(

let uu____5895 = (trans_F_ env arg wp_arg)
in ((uu____5895), (q)));
))
end)) args wp_args)
in ((head), (uu____5855)))
in FStar_Syntax_Syntax.Tm_app (uu____5845))
in (mk uu____5844));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let uu____5917 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____5917) with
| (binders_orig, comp) -> begin
(

let uu____5922 = (

let uu____5930 = (FStar_List.map (fun uu____5944 -> (match (uu____5944) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____5957 = (is_C h)
in (match (uu____5957) with
| true -> begin
(

let w' = (

let uu____5964 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None uu____5964))
in (

let uu____5965 = (

let uu____5969 = (

let uu____5973 = (

let uu____5976 = (

let uu____5977 = (

let uu____5978 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h uu____5978))
in (FStar_Syntax_Syntax.null_bv uu____5977))
in ((uu____5976), (q)))
in (uu____5973)::[])
in (((w'), (q)))::uu____5969)
in ((w'), (uu____5965))))
end
| uu____5988 -> begin
(

let x = (

let uu____5990 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None uu____5990))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig)
in (FStar_List.split uu____5930))
in (match (uu____5922) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (

let uu____6020 = (

let uu____6022 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig uu____6022))
in (FStar_Syntax_Subst.subst_comp uu____6020 comp))
in (

let app = (

let uu____6026 = (

let uu____6027 = (

let uu____6037 = (FStar_List.map (fun bv -> (

let uu____6044 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____6045 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____6044), (uu____6045))))) bvs)
in ((wp), (uu____6037)))
in FStar_Syntax_Syntax.Tm_app (uu____6027))
in (mk uu____6026))
in (

let comp = (

let uu____6050 = (type_of_comp comp)
in (

let uu____6051 = (is_monadic_comp comp)
in (trans_G env uu____6050 uu____6051 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____6053, uu____6054) -> begin
(trans_F_ env e wp)
end
| uu____6073 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in (match (is_monadic) with
| true -> begin
(

let uu____6088 = (

let uu____6089 = (star_type' env h)
in (

let uu____6092 = (

let uu____6098 = (

let uu____6101 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (uu____6101)))
in (uu____6098)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu____6089; FStar_Syntax_Syntax.effect_args = uu____6092; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____6088))
end
| uu____6106 -> begin
(

let uu____6107 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total uu____6107))
end)))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (

let uu____6118 = (n env.env t)
in (star_type' env uu____6118)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (

let uu____6130 = (n env.env t)
in (check_n env uu____6130)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let uu____6140 = (n env.env c)
in (

let uu____6141 = (n env.env wp)
in (trans_F_ env uu____6140 uu____6141))))




