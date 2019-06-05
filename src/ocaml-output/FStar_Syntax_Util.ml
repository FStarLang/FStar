
open Prims
open FStar_Pervasives

let tts_f : (FStar_Syntax_Syntax.term  ->  Prims.string) FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let tts : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let uu____26 = (FStar_ST.op_Bang tts_f)
in (match (uu____26) with
| FStar_Pervasives_Native.None -> begin
"<<hook unset>>"
end
| FStar_Pervasives_Native.Some (f) -> begin
(f t)
end)))


let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id1 -> (

let uu____90 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id1)::[])))
in (FStar_Ident.set_lid_range uu____90 id1.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (

let uu____97 = (

let uu____100 = (

let uu____103 = (FStar_Ident.mk_ident (((Prims.op_Hat FStar_Ident.reserved_prefix (Prims.op_Hat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (uu____103)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____100))
in (FStar_Ident.lid_of_ids uu____97)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____121 . (FStar_Syntax_Syntax.bv * 'Auu____121)  ->  (FStar_Syntax_Syntax.term * 'Auu____121) = (fun uu____134 -> (match (uu____134) with
| (b, imp) -> begin
(

let uu____141 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____141), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____193 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____193) with
| true -> begin
[]
end
| uu____210 -> begin
(

let uu____212 = (arg_of_non_null_binder b)
in (uu____212)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____247 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____329 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____329) with
| true -> begin
(

let b1 = (

let uu____355 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____355), ((FStar_Pervasives_Native.snd b))))
in (

let uu____362 = (arg_of_non_null_binder b1)
in ((b1), (uu____362))))
end
| uu____383 -> begin
(

let uu____385 = (arg_of_non_null_binder b)
in ((b), (uu____385)))
end)))))
in (FStar_All.pipe_right uu____247 FStar_List.unzip)))


let name_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____519 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____519) with
| true -> begin
(

let uu____528 = b
in (match (uu____528) with
| (a, imp) -> begin
(

let b1 = (

let uu____548 = (

let uu____550 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "_" uu____550))
in (FStar_Ident.id_of_text uu____548))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____557 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____595 = (

let uu____602 = (

let uu____603 = (

let uu____618 = (name_binders binders)
in ((uu____618), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____603))
in (FStar_Syntax_Syntax.mk uu____602))
in (uu____595 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____637 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____674 -> (match (uu____674) with
| (t, imp) -> begin
(

let uu____685 = (

let uu____686 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____686))
in ((uu____685), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____741 -> (match (uu____741) with
| (t, imp) -> begin
(

let uu____758 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____758), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____771 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____771 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____783 . 'Auu____783  ->  'Auu____783 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____863 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____909 uu____910 -> (match (((uu____909), (uu____910))) with
| ((x, uu____936), (y, uu____938)) -> begin
(

let uu____959 = (

let uu____966 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____966)))
in FStar_Syntax_Syntax.NT (uu____959))
end)) replace_xs with_ys)
end
| uu____971 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____982) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____988, uu____989) -> begin
(unmeta e2)
end
| uu____1030 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____1044) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____1051) -> begin
e1
end
| uu____1060 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1062, uu____1063) -> begin
(unmeta_safe e2)
end
| uu____1104 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____1123) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____1126) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____1140 = (univ_kernel u1)
in (match (uu____1140) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____1157) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____1166) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____1181 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____1181)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____1201), uu____1202) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____1206, FStar_Syntax_Syntax.U_bvar (uu____1207)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____1212) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1214, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____1217) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1219, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____1223), FStar_Syntax_Syntax.U_unif (uu____1224)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____1234), FStar_Syntax_Syntax.U_name (uu____1235)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____1263 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____1265 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____1263 - uu____1265)))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in (match ((Prims.op_disEquality n1 n2)) with
| true -> begin
(n1 - n2)
end
| uu____1277 -> begin
(

let copt = (

let uu____1283 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____1283 (fun uu____1299 -> (match (uu____1299) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1318 -> begin
FStar_Pervasives_Native.None
end))
end))))
in (match (copt) with
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "0")
end
| FStar_Pervasives_Native.Some (c) -> begin
c
end))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____1327), uu____1328) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1332, FStar_Syntax_Syntax.U_max (uu____1333)) -> begin
(Prims.parse_int "1")
end
| uu____1337 -> begin
(

let uu____1342 = (univ_kernel u1)
in (match (uu____1342) with
| (k1, n1) -> begin
(

let uu____1353 = (univ_kernel u2)
in (match (uu____1353) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____1370 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____1384 = (compare_univs u1 u2)
in (Prims.op_Equality uu____1384 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (

let uu____1403 = (

let uu____1404 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = uu____1404; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp uu____1403)))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____1424) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____1433) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1456) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1465) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_to_comp_typ_nouniv : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1
end
| FStar_Syntax_Syntax.Total (t, u_opt) -> begin
(

let uu____1492 = (

let uu____1493 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1493))
in {FStar_Syntax_Syntax.comp_univs = uu____1492; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1522 = (

let uu____1523 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1523))
in {FStar_Syntax_Syntax.comp_univs = uu____1522; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let uu___229_1559 = c
in (

let uu____1560 = (

let uu____1561 = (

let uu___231_1562 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___231_1562.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___231_1562.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___231_1562.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___231_1562.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1561))
in {FStar_Syntax_Syntax.n = uu____1560; FStar_Syntax_Syntax.pos = uu___229_1559.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___229_1559.FStar_Syntax_Syntax.vars})))


let lcomp_set_flags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun lc fs -> (

let comp_typ_set_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1588) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____1597) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___243_1608 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___243_1608.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___243_1608.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___243_1608.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___243_1608.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = fs})
in (

let uu___246_1609 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___246_1609.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___246_1609.FStar_Syntax_Syntax.vars}))
end))
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ fs (fun uu____1612 -> (

let uu____1613 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_typ_set_flags uu____1613))))))


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some (u)) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| uu____1653 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1668) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1678) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___0_1703 -> (match (uu___0_1703) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1707 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___1_1720 -> (match (uu___1_1720) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1724 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___2_1737 -> (match (uu___2_1737) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1741 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___3_1758 -> (match (uu___3_1758) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1762 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___4_1775 -> (match (uu___4_1775) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1779 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1811) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1821) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___5_1836 -> (match (uu___5_1836) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1839 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_or_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> ((is_pure_effect l) || (is_ghost_effect l)))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___6_1884 -> (match (uu___6_1884) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1887 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1903 = (

let uu____1904 = (FStar_Syntax_Subst.compress t)
in uu____1904.FStar_Syntax_Syntax.n)
in (match (uu____1903) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1908, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1930 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1945 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1954 = (

let uu____1955 = (FStar_Syntax_Subst.compress t)
in uu____1955.FStar_Syntax_Syntax.n)
in (match (uu____1954) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1959, c) -> begin
(is_lemma_comp c)
end
| uu____1981 -> begin
false
end)))


let rec head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1989 = (

let uu____1990 = (FStar_Syntax_Subst.compress t)
in uu____1990.FStar_Syntax_Syntax.n)
in (match (uu____1989) with
| FStar_Syntax_Syntax.Tm_app (t1, uu____1994) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_match (t1, uu____2020) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_abs (uu____2057, t1, uu____2059) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2085, uu____2086) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____2128) -> begin
(head_of t1)
end
| uu____2133 -> begin
t
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____2211 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____2293 = (head_and_args' head1)
in (match (uu____2293) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____2362 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2389) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____2394 -> begin
t1
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___7_2412 -> (match (uu___7_2412) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2415 -> begin
false
end)))))
end
| uu____2417 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____2434) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____2444) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2473) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____2482) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___399_2494 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___399_2494.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___399_2494.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___399_2494.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___399_2494.FStar_Syntax_Syntax.flags}))
end))


let set_result_typ_lc : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____2508 -> (

let uu____2509 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (set_result_typ uu____2509 t)))))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___8_2527 -> (match (uu___8_2527) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2531 -> begin
false
end)))))


let comp_effect_args : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.args = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2539) -> begin
[]
end
| FStar_Syntax_Syntax.GTotal (uu____2556) -> begin
[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.effect_args
end))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2600 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2610, uu____2611) -> begin
(unascribe e2)
end
| uu____2652 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2705, uu____2706) -> begin
(ascribe t' k)
end
| uu____2747 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2774 = (

let uu____2783 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2783))
in (uu____2774 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2839 = (

let uu____2840 = (FStar_Syntax_Subst.compress t)
in uu____2840.FStar_Syntax_Syntax.n)
in (match (uu____2839) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2844 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2844))
end
| uu____2845 -> begin
t
end)))


let rec unlazy_emb : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2852 = (

let uu____2853 = (FStar_Syntax_Subst.compress t)
in uu____2853.FStar_Syntax_Syntax.n)
in (match (uu____2852) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(match (i.FStar_Syntax_Syntax.lkind) with
| FStar_Syntax_Syntax.Lazy_embedding (uu____2857) -> begin
(

let uu____2866 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2866))
end
| uu____2867 -> begin
t
end)
end
| uu____2868 -> begin
t
end)))


let eq_lazy_kind : FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.lazy_kind  ->  Prims.bool = (fun k k' -> (match (((k), (k'))) with
| (FStar_Syntax_Syntax.BadLazy, FStar_Syntax_Syntax.BadLazy) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_bv, FStar_Syntax_Syntax.Lazy_bv) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_binder, FStar_Syntax_Syntax.Lazy_binder) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_fvar, FStar_Syntax_Syntax.Lazy_fvar) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_comp, FStar_Syntax_Syntax.Lazy_comp) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_env, FStar_Syntax_Syntax.Lazy_env) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_proofstate, FStar_Syntax_Syntax.Lazy_proofstate) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_goal, FStar_Syntax_Syntax.Lazy_goal) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_sigelt, FStar_Syntax_Syntax.Lazy_sigelt) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_uvar, FStar_Syntax_Syntax.Lazy_uvar) -> begin
true
end
| uu____2892 -> begin
false
end))


let rec unlazy_as_t : 'Auu____2905 . FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.term  ->  'Auu____2905 = (fun k t -> (

let uu____2916 = (

let uu____2917 = (FStar_Syntax_Subst.compress t)
in uu____2917.FStar_Syntax_Syntax.n)
in (match (uu____2916) with
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k'; FStar_Syntax_Syntax.ltyp = uu____2922; FStar_Syntax_Syntax.rng = uu____2923}) when (eq_lazy_kind k k') -> begin
(FStar_Dyn.undyn v1)
end
| uu____2926 -> begin
(failwith "Not a Tm_lazy of the expected kind")
end)))


let mk_lazy : 'a . 'a  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lazy_kind  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun t typ k r -> (

let rng = (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
r1
end
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end)
in (

let i = (

let uu____2967 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2967; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.ltyp = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2980 = (

let uu____2995 = (unascribe t)
in (head_and_args' uu____2995))
in (match (uu____2980) with
| (hd1, args) -> begin
(FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end)))

type eq_result =
| Equal
| NotEqual
| Unknown


let uu___is_Equal : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equal -> begin
true
end
| uu____3029 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____3040 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____3051 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let eq_inj : eq_result  ->  eq_result  ->  eq_result = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____3101) -> begin
NotEqual
end
| (uu____3102, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____3103) -> begin
Unknown
end
| (uu____3104, Unknown) -> begin
Unknown
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___9_3225 -> (match (uu___9_3225) with
| true -> begin
Equal
end
| uu____3228 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___10_3236 -> (match (uu___10_3236) with
| true -> begin
Equal
end
| uu____3239 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____3257 -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____3279 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____3279) with
| true -> begin
(

let uu____3283 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____3360 -> (match (uu____3360) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____3401 = (eq_tm a1 a2)
in (eq_inj acc uu____3401))
end)) Equal) uu____3283))
end
| uu____3402 -> begin
NotEqual
end)))
in (

let heads_and_args_in_case_both_data = (

let uu____3415 = (

let uu____3432 = (FStar_All.pipe_right t11 unmeta)
in (FStar_All.pipe_right uu____3432 head_and_args))
in (match (uu____3415) with
| (head1, args1) -> begin
(

let uu____3485 = (

let uu____3502 = (FStar_All.pipe_right t21 unmeta)
in (FStar_All.pipe_right uu____3502 head_and_args))
in (match (uu____3485) with
| (head2, args2) -> begin
(

let uu____3555 = (

let uu____3560 = (

let uu____3561 = (un_uinst head1)
in uu____3561.FStar_Syntax_Syntax.n)
in (

let uu____3564 = (

let uu____3565 = (un_uinst head2)
in uu____3565.FStar_Syntax_Syntax.n)
in ((uu____3560), (uu____3564))))
in (match (uu____3555) with
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) when ((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
FStar_Pervasives_Native.Some (((f), (args1), (g), (args2)))
end
| uu____3592 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
in (

let uu____3605 = (

let uu____3610 = (

let uu____3611 = (unmeta t11)
in uu____3611.FStar_Syntax_Syntax.n)
in (

let uu____3614 = (

let uu____3615 = (unmeta t21)
in uu____3615.FStar_Syntax_Syntax.n)
in ((uu____3610), (uu____3614))))
in (match (uu____3605) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____3621), uu____3622) -> begin
(

let uu____3623 = (unlazy t11)
in (eq_tm uu____3623 t21))
end
| (uu____3624, FStar_Syntax_Syntax.Tm_lazy (uu____3625)) -> begin
(

let uu____3626 = (unlazy t21)
in (eq_tm t11 uu____3626))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| uu____3629 when (FStar_All.pipe_right heads_and_args_in_case_both_data FStar_Util.is_some) -> begin
(

let uu____3653 = (FStar_All.pipe_right heads_and_args_in_case_both_data FStar_Util.must)
in (FStar_All.pipe_right uu____3653 (fun uu____3701 -> (match (uu____3701) with
| (f, args1, g, args2) -> begin
(equal_data f args1 g args2)
end))))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3716 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____3716))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____3730 = (eq_tm f g)
in (eq_and uu____3730 (fun uu____3733 -> (

let uu____3734 = (eq_univs_list us vs)
in (equal_if uu____3734)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3736)), uu____3737) -> begin
Unknown
end
| (uu____3738, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3739))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____3742 = (FStar_Const.eq_const c d)
in (equal_iff uu____3742))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu____3745)), FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu____3747))) -> begin
(

let uu____3776 = (FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head)
in (equal_if uu____3776))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____3830 = (

let uu____3835 = (

let uu____3836 = (un_uinst h1)
in uu____3836.FStar_Syntax_Syntax.n)
in (

let uu____3839 = (

let uu____3840 = (un_uinst h2)
in uu____3840.FStar_Syntax_Syntax.n)
in ((uu____3835), (uu____3839))))
in (match (uu____3830) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____3846 = (

let uu____3848 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____3848))
in (FStar_List.mem uu____3846 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____3850 -> begin
(

let uu____3855 = (eq_tm h1 h2)
in (eq_and uu____3855 (fun uu____3857 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____3963 = (FStar_List.zip bs1 bs2)
in (

let uu____4026 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____4063 a -> (match (uu____4063) with
| (b1, b2) -> begin
(eq_and a (fun uu____4156 -> (branch_matches b1 b2)))
end)) uu____3963 uu____4026)))
end
| uu____4157 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____4161 = (eq_univs u v1)
in (equal_if uu____4161))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(

let uu____4175 = (eq_quoteinfo q1 q2)
in (eq_and uu____4175 (fun uu____4177 -> (eq_tm t12 t22))))
end
| (FStar_Syntax_Syntax.Tm_refine (t12, phi1), FStar_Syntax_Syntax.Tm_refine (t22, phi2)) -> begin
(

let uu____4190 = (eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort)
in (eq_and uu____4190 (fun uu____4192 -> (eq_tm phi1 phi2))))
end
| uu____4193 -> begin
Unknown
end))))))))))
and eq_quoteinfo : FStar_Syntax_Syntax.quoteinfo  ->  FStar_Syntax_Syntax.quoteinfo  ->  eq_result = (fun q1 q2 -> (match ((Prims.op_disEquality q1.FStar_Syntax_Syntax.qkind q2.FStar_Syntax_Syntax.qkind)) with
| true -> begin
NotEqual
end
| uu____4201 -> begin
(eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes q2.FStar_Syntax_Syntax.antiquotes)
end))
and eq_antiquotes : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| ([], uu____4265) -> begin
NotEqual
end
| (uu____4296, []) -> begin
NotEqual
end
| (((x1, t1))::a11, ((x2, t2))::a21) -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x1 x2)))) with
| true -> begin
NotEqual
end
| uu____4386 -> begin
(

let uu____4388 = (eq_tm t1 t2)
in (match (uu____4388) with
| NotEqual -> begin
NotEqual
end
| Unknown -> begin
(

let uu____4389 = (eq_antiquotes a11 a21)
in (match (uu____4389) with
| NotEqual -> begin
NotEqual
end
| uu____4390 -> begin
Unknown
end))
end
| Equal -> begin
(eq_antiquotes a11 a21)
end))
end)
end))
and eq_aqual : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
Equal
end
| (FStar_Pervasives_Native.None, uu____4405) -> begin
NotEqual
end
| (uu____4412, FStar_Pervasives_Native.None) -> begin
NotEqual
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b1)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b2))) when (Prims.op_Equality b1 b2) -> begin
Equal
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t1)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t2))) -> begin
(eq_tm t1 t2)
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) -> begin
Equal
end
| uu____4442 -> begin
NotEqual
end))
and branch_matches : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  eq_result = (fun b1 b2 -> (

let related_by = (fun f o1 o2 -> (match (((o1), (o2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(f x y)
end
| (uu____4534, uu____4535) -> begin
false
end))
in (

let uu____4545 = b1
in (match (uu____4545) with
| (p1, w1, t1) -> begin
(

let uu____4579 = b2
in (match (uu____4579) with
| (p2, w2, t2) -> begin
(

let uu____4613 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____4613) with
| true -> begin
(

let uu____4616 = ((

let uu____4620 = (eq_tm t1 t2)
in (Prims.op_Equality uu____4620 Equal)) && (related_by (fun t11 t21 -> (

let uu____4629 = (eq_tm t11 t21)
in (Prims.op_Equality uu____4629 Equal))) w1 w2))
in (match (uu____4616) with
| true -> begin
Equal
end
| uu____4631 -> begin
Unknown
end))
end
| uu____4633 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____4694))::a11, ((b, uu____4697))::b1) -> begin
(

let uu____4771 = (eq_tm a b)
in (match (uu____4771) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____4772 -> begin
Unknown
end))
end
| uu____4773 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____4809) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4815, uu____4816) -> begin
(unrefine t2)
end
| uu____4857 -> begin
t1
end)))


let rec is_uvar : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4865 = (

let uu____4866 = (FStar_Syntax_Subst.compress t)
in uu____4866.FStar_Syntax_Syntax.n)
in (match (uu____4865) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4870) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4885) -> begin
(is_uvar t1)
end
| FStar_Syntax_Syntax.Tm_app (uu____4890) -> begin
(

let uu____4907 = (

let uu____4908 = (FStar_All.pipe_right t head_and_args)
in (FStar_All.pipe_right uu____4908 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4907 is_uvar))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4971, uu____4972) -> begin
(is_uvar t1)
end
| uu____5013 -> begin
false
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5022 = (

let uu____5023 = (unrefine t)
in uu____5023.FStar_Syntax_Syntax.n)
in (match (uu____5022) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____5029) -> begin
(is_unit head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5055) -> begin
(is_unit t1)
end
| uu____5060 -> begin
false
end)))


let is_eqtype_no_unrefine : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5069 = (

let uu____5070 = (FStar_Syntax_Subst.compress t)
in uu____5070.FStar_Syntax_Syntax.n)
in (match (uu____5069) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid)
end
| uu____5075 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5084 = (

let uu____5085 = (unrefine t)
in uu____5085.FStar_Syntax_Syntax.n)
in (match (uu____5084) with
| FStar_Syntax_Syntax.Tm_type (uu____5089) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____5093) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5119) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5124, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____5146 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____5155 = (

let uu____5156 = (FStar_Syntax_Subst.compress e)
in uu____5156.FStar_Syntax_Syntax.n)
in (match (uu____5155) with
| FStar_Syntax_Syntax.Tm_abs (uu____5160) -> begin
true
end
| uu____5180 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5189 = (

let uu____5190 = (FStar_Syntax_Subst.compress t)
in uu____5190.FStar_Syntax_Syntax.n)
in (match (uu____5189) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5194) -> begin
true
end
| uu____5210 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____5220) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5226, uu____5227) -> begin
(pre_typ t2)
end
| uu____5268 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____5293 = (

let uu____5294 = (un_uinst typ1)
in uu____5294.FStar_Syntax_Syntax.n)
in (match (uu____5293) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____5359 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____5389 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____5410, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____5417) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____5422, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5433, uu____5434, uu____5435, uu____5436, uu____5437) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____5447, uu____5448, uu____5449, uu____5450) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____5456, uu____5457, uu____5458, uu____5459, uu____5460) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5468, uu____5469) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____5471, uu____5472) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____5475) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____5476) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____5477) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____5491 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___11_5517 -> (match (uu___11_5517) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____5531 'Auu____5532 . ('Auu____5531 FStar_Syntax_Syntax.syntax * 'Auu____5532)  ->  FStar_Range.range = (fun uu____5543 -> (match (uu____5543) with
| (hd1, uu____5551) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____5565 'Auu____5566 . ('Auu____5565 FStar_Syntax_Syntax.syntax * 'Auu____5566) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____5664 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_app_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f bs -> (

let uu____5723 = (FStar_List.map (fun uu____5750 -> (match (uu____5750) with
| (bv, aq) -> begin
(

let uu____5769 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5769), (aq)))
end)) bs)
in (mk_app f uu____5723)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____5819 = (FStar_Ident.range_of_lid l)
in (

let uu____5820 = (

let uu____5829 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____5829))
in (uu____5820 FStar_Pervasives_Native.None uu____5819)))
end
| uu____5834 -> begin
(

let e = (

let uu____5848 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____5848 args))
in (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let field_projector_prefix : Prims.string = "__proj__"


let field_projector_sep : Prims.string = "__item__"


let field_projector_contains_constructor : Prims.string  ->  Prims.bool = (fun s -> (FStar_Util.starts_with s field_projector_prefix))


let mk_field_projector_name_from_string : Prims.string  ->  Prims.string  ->  Prims.string = (fun constr field -> (Prims.op_Hat field_projector_prefix (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))))


let mk_field_projector_name_from_ident : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid i -> (

let itext = i.FStar_Ident.idText
in (

let newi = (match ((field_projector_contains_constructor itext)) with
| true -> begin
i
end
| uu____5899 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText itext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[]))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____5925 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5925) with
| true -> begin
(

let uu____5928 = (

let uu____5934 = (

let uu____5936 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "_" uu____5936))
in (

let uu____5939 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____5934), (uu____5939))))
in (FStar_Ident.mk_ident uu____5928))
end
| uu____5941 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___993_5944 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___993_5944.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___993_5944.FStar_Syntax_Syntax.sort})
in (

let uu____5945 = (mk_field_projector_name_from_ident lid nm)
in ((uu____5945), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____5957) -> begin
ses
end
| uu____5966 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____5977 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____5990 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____5990) with
| FStar_Pervasives_Native.Some (uu____5993) -> begin
(

let uu____5994 = (

let uu____5996 = (

let uu____5998 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5998))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5996))
in (failwith uu____5994))
end
| uu____6003 -> begin
(FStar_Syntax_Unionfind.change uv t)
end)))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (Prims.op_Equality l1b.FStar_Ident.idText l2b.FStar_Ident.idText))
end
| (FStar_Syntax_Syntax.RecordType (ns1, f1), FStar_Syntax_Syntax.RecordType (ns2, f2)) -> begin
((((Prims.op_Equality (FStar_List.length ns1) (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2)) && (Prims.op_Equality (FStar_List.length f1) (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2))
end
| (FStar_Syntax_Syntax.RecordConstructor (ns1, f1), FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) -> begin
((((Prims.op_Equality (FStar_List.length ns1) (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2)) && (Prims.op_Equality (FStar_List.length f1) (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2))
end
| uu____6086 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____6132 = (

let uu___1054_6133 = rc
in (

let uu____6134 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___1054_6133.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6134; FStar_Syntax_Syntax.residual_flags = uu___1054_6133.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____6132))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____6151 -> begin
(

let body = (

let uu____6153 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____6153))
in (match (body.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt') -> begin
(

let uu____6183 = (

let uu____6190 = (

let uu____6191 = (

let uu____6210 = (

let uu____6219 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____6219 bs'))
in (

let uu____6234 = (close_lopt lopt')
in ((uu____6210), (t1), (uu____6234))))
in FStar_Syntax_Syntax.Tm_abs (uu____6191))
in (FStar_Syntax_Syntax.mk uu____6190))
in (uu____6183 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____6249 -> begin
(

let uu____6250 = (

let uu____6257 = (

let uu____6258 = (

let uu____6277 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____6286 = (close_lopt lopt)
in ((uu____6277), (body), (uu____6286))))
in FStar_Syntax_Syntax.Tm_abs (uu____6258))
in (FStar_Syntax_Syntax.mk uu____6257))
in (uu____6250 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____6342 -> begin
(

let uu____6351 = (

let uu____6358 = (

let uu____6359 = (

let uu____6374 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____6383 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____6374), (uu____6383))))
in FStar_Syntax_Syntax.Tm_arrow (uu____6359))
in (FStar_Syntax_Syntax.mk uu____6358))
in (uu____6351 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____6432 = (

let uu____6433 = (FStar_Syntax_Subst.compress t)
in uu____6433.FStar_Syntax_Syntax.n)
in (match (uu____6432) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____6463) -> begin
(

let uu____6472 = (

let uu____6473 = (FStar_Syntax_Subst.compress tres)
in uu____6473.FStar_Syntax_Syntax.n)
in (match (uu____6472) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____6516 -> begin
t
end))
end
| uu____6517 -> begin
t
end)
end
| uu____6518 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____6536 = (

let uu____6537 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____6537 t.FStar_Syntax_Syntax.pos))
in (

let uu____6538 = (

let uu____6545 = (

let uu____6546 = (

let uu____6553 = (

let uu____6556 = (

let uu____6557 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____6557)::[])
in (FStar_Syntax_Subst.close uu____6556 t))
in ((b), (uu____6553)))
in FStar_Syntax_Syntax.Tm_refine (uu____6546))
in (FStar_Syntax_Syntax.mk uu____6545))
in (uu____6538 FStar_Pervasives_Native.None uu____6536))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6637 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6637) with
| (bs1, c1) -> begin
(

let uu____6656 = (is_total_comp c1)
in (match (uu____6656) with
| true -> begin
(

let uu____6671 = (arrow_formals_comp (comp_result c1))
in (match (uu____6671) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____6728 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6738; FStar_Syntax_Syntax.index = uu____6739; FStar_Syntax_Syntax.sort = s}, uu____6741) -> begin
(

let rec aux = (fun s1 k2 -> (

let uu____6772 = (

let uu____6773 = (FStar_Syntax_Subst.compress s1)
in uu____6773.FStar_Syntax_Syntax.n)
in (match (uu____6772) with
| FStar_Syntax_Syntax.Tm_arrow (uu____6788) -> begin
(arrow_formals_comp s1)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6803; FStar_Syntax_Syntax.index = uu____6804; FStar_Syntax_Syntax.sort = s2}, uu____6806) -> begin
(aux s2 k2)
end
| uu____6814 -> begin
(

let uu____6815 = (FStar_Syntax_Syntax.mk_Total k2)
in (([]), (uu____6815)))
end)))
in (aux s k1))
end
| uu____6830 -> begin
(

let uu____6831 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____6831)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____6866 = (arrow_formals_comp k)
in (match (uu____6866) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let let_rec_arity : FStar_Syntax_Syntax.letbinding  ->  (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option) = (fun lb -> (

let rec arrow_until_decreases = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____7008 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7008) with
| (bs1, c1) -> begin
(

let ct = (comp_to_comp_typ c1)
in (

let uu____7032 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.find_opt (fun uu___12_7041 -> (match (uu___12_7041) with
| FStar_Syntax_Syntax.DECREASES (uu____7043) -> begin
true
end
| uu____7047 -> begin
false
end))))
in (match (uu____7032) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (d)) -> begin
((bs1), (FStar_Pervasives_Native.Some (d)))
end
| uu____7082 -> begin
(

let uu____7085 = (is_total_comp c1)
in (match (uu____7085) with
| true -> begin
(

let uu____7104 = (arrow_until_decreases (comp_result c1))
in (match (uu____7104) with
| (bs', d) -> begin
(((FStar_List.append bs1 bs')), (d))
end))
end
| uu____7181 -> begin
((bs1), (FStar_Pervasives_Native.None))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____7197; FStar_Syntax_Syntax.index = uu____7198; FStar_Syntax_Syntax.sort = k2}, uu____7200) -> begin
(arrow_until_decreases k2)
end
| uu____7208 -> begin
(([]), (FStar_Pervasives_Native.None))
end)))
in (

let uu____7229 = (arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____7229) with
| (bs, dopt) -> begin
(

let n_univs = (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
in (

let uu____7283 = (FStar_Util.map_opt dopt (fun d -> (

let d_bvs = (FStar_Syntax_Free.names d)
in (

let uu____7304 = (FStar_Common.tabulate n_univs (fun uu____7310 -> false))
in (

let uu____7313 = (FStar_All.pipe_right bs (FStar_List.map (fun uu____7338 -> (match (uu____7338) with
| (x, uu____7347) -> begin
(FStar_Util.set_mem x d_bvs)
end))))
in (FStar_List.append uu____7304 uu____7313))))))
in (((n_univs + (FStar_List.length bs))), (uu____7283))))
end))))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____7403 = (

let uu___1176_7404 = rc
in (

let uu____7405 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___1176_7404.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____7405; FStar_Syntax_Syntax.residual_flags = uu___1176_7404.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____7403))
end
| uu____7414 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____7448 = (

let uu____7449 = (

let uu____7452 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____7452))
in uu____7449.FStar_Syntax_Syntax.n)
in (match (uu____7448) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____7498 = (aux t2 what)
in (match (uu____7498) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____7570 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____7587 = (aux t FStar_Pervasives_Native.None)
in (match (uu____7587) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____7635 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____7635) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____7798) -> begin
def
end
| (uu____7809, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____7821) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _7837 -> FStar_Syntax_Syntax.U_name (_7837))))
in (

let inst1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst1 def)))
end)
in (

let typ1 = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def2 = (FStar_Syntax_Subst.close_univ_vars univ_vars def1)
in (mk_letbinding lbname univ_vars typ1 eff def2 attrs pos)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____7919 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____7919) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____7954 -> begin
(

let t' = (arrow binders c)
in (

let uu____7966 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____7966) with
| (uvs1, t'1) -> begin
(

let uu____7987 = (

let uu____7988 = (FStar_Syntax_Subst.compress t'1)
in uu____7988.FStar_Syntax_Syntax.n)
in (match (uu____7987) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____8037 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____8062 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____8073 -> begin
false
end))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality : FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.not_lid)::(FStar_Parser_Const.iff_lid)::(FStar_Parser_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____8136 = (

let uu____8137 = (pre_typ t)
in uu____8137.FStar_Syntax_Syntax.n)
in (match (uu____8136) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____8142 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____8156 = (

let uu____8157 = (pre_typ t)
in uu____8157.FStar_Syntax_Syntax.n)
in (match (uu____8156) with
| FStar_Syntax_Syntax.Tm_fvar (uu____8161) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____8163) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____8189) -> begin
(is_constructed_typ t1 lid)
end
| uu____8194 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____8207) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____8208) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8209) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____8211) -> begin
(get_tycon t2)
end
| uu____8236 -> begin
FStar_Pervasives_Native.None
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____8244 = (

let uu____8245 = (un_uinst t)
in uu____8245.FStar_Syntax_Syntax.n)
in (match (uu____8244) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____8250 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____8264 = (

let uu____8268 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____8268))
in (match (uu____8264) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____8300 -> begin
false
end))
end
| uu____8305 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____8319 -> (

let u = (

let uu____8325 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _8342 -> FStar_Syntax_Syntax.U_unif (_8342)) uu____8325))
in (

let uu____8343 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____8343), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____8356 = (eq_tm a a')
in (match (uu____8356) with
| Equal -> begin
true
end
| uu____8359 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____8364 = (

let uu____8371 = (

let uu____8372 = (

let uu____8373 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____8373 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____8372))
in (FStar_Syntax_Syntax.mk uu____8371))
in (uu____8364 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_true_bool : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_char : FStar_BaseTypes.char  ->  FStar_Syntax_Syntax.term = (fun c -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.bool_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.not_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.true_lid)


let tac_opaque_attr : FStar_Syntax_Syntax.term = (exp_string "tac_opaque")


let dm4f_bind_range_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.dm4f_bind_range_attr)


let tcdecltime_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.tcdecltime_attr)


let inline_let_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.inline_let_attr)


let t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____8485 = (

let uu____8488 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____8489 = (

let uu____8496 = (

let uu____8497 = (

let uu____8514 = (

let uu____8525 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____8534 = (

let uu____8545 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____8545)::[])
in (uu____8525)::uu____8534))
in ((tand), (uu____8514)))
in FStar_Syntax_Syntax.Tm_app (uu____8497))
in (FStar_Syntax_Syntax.mk uu____8496))
in (uu____8489 FStar_Pervasives_Native.None uu____8488)))
in FStar_Pervasives_Native.Some (uu____8485))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____8622 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____8623 = (

let uu____8630 = (

let uu____8631 = (

let uu____8648 = (

let uu____8659 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____8668 = (

let uu____8679 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____8679)::[])
in (uu____8659)::uu____8668))
in ((op_t), (uu____8648)))
in FStar_Syntax_Syntax.Tm_app (uu____8631))
in (FStar_Syntax_Syntax.mk uu____8630))
in (uu____8623 FStar_Pervasives_Native.None uu____8622))))


let mk_neg : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____8736 = (

let uu____8743 = (

let uu____8744 = (

let uu____8761 = (

let uu____8772 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____8772)::[])
in ((t_not), (uu____8761)))
in FStar_Syntax_Syntax.Tm_app (uu____8744))
in (FStar_Syntax_Syntax.mk uu____8743))
in (uu____8736 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_conj tl1 hd1)
end))


let mk_disj : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_disj tl1 hd1)
end))


let mk_imp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop timp phi1 phi2))


let mk_iff : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e -> (

let uu____8969 = (

let uu____8976 = (

let uu____8977 = (

let uu____8994 = (

let uu____9005 = (FStar_Syntax_Syntax.as_arg e)
in (uu____9005)::[])
in ((b2t_v), (uu____8994)))
in FStar_Syntax_Syntax.Tm_app (uu____8977))
in (FStar_Syntax_Syntax.mk uu____8976))
in (uu____8969 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let unb2t : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e -> (

let uu____9052 = (head_and_args e)
in (match (uu____9052) with
| (hd1, args) -> begin
(

let uu____9097 = (

let uu____9112 = (

let uu____9113 = (FStar_Syntax_Subst.compress hd1)
in uu____9113.FStar_Syntax_Syntax.n)
in ((uu____9112), (args)))
in (match (uu____9097) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e1, uu____9130))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid) -> begin
FStar_Pervasives_Native.Some (e1)
end
| uu____9165 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_t_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9187 = (

let uu____9188 = (unmeta t)
in uu____9188.FStar_Syntax_Syntax.n)
in (match (uu____9187) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____9193 -> begin
false
end)))


let mk_conj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____9216 = (is_t_true t1)
in (match (uu____9216) with
| true -> begin
t2
end
| uu____9221 -> begin
(

let uu____9223 = (is_t_true t2)
in (match (uu____9223) with
| true -> begin
t1
end
| uu____9228 -> begin
(mk_conj t1 t2)
end))
end)))


let mk_disj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____9251 = (is_t_true t1)
in (match (uu____9251) with
| true -> begin
t_true
end
| uu____9256 -> begin
(

let uu____9258 = (is_t_true t2)
in (match (uu____9258) with
| true -> begin
t_true
end
| uu____9263 -> begin
(mk_disj t1 t2)
end))
end)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____9287 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____9288 = (

let uu____9295 = (

let uu____9296 = (

let uu____9313 = (

let uu____9324 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____9333 = (

let uu____9344 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____9344)::[])
in (uu____9324)::uu____9333))
in ((teq), (uu____9313)))
in FStar_Syntax_Syntax.Tm_app (uu____9296))
in (FStar_Syntax_Syntax.mk uu____9295))
in (uu____9288 FStar_Pervasives_Native.None uu____9287))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____9411 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____9412 = (

let uu____9419 = (

let uu____9420 = (

let uu____9437 = (

let uu____9448 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9457 = (

let uu____9468 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____9477 = (

let uu____9488 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____9488)::[])
in (uu____9468)::uu____9477))
in (uu____9448)::uu____9457))
in ((eq_inst), (uu____9437)))
in FStar_Syntax_Syntax.Tm_app (uu____9420))
in (FStar_Syntax_Syntax.mk uu____9419))
in (uu____9412 FStar_Pervasives_Native.None uu____9411)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____9565 = (

let uu____9572 = (

let uu____9573 = (

let uu____9590 = (

let uu____9601 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9610 = (

let uu____9621 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____9630 = (

let uu____9641 = (FStar_Syntax_Syntax.as_arg t')
in (uu____9641)::[])
in (uu____9621)::uu____9630))
in (uu____9601)::uu____9610))
in ((t_has_type1), (uu____9590)))
in FStar_Syntax_Syntax.Tm_app (uu____9573))
in (FStar_Syntax_Syntax.mk uu____9572))
in (uu____9565 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____9718 = (

let uu____9725 = (

let uu____9726 = (

let uu____9743 = (

let uu____9754 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9763 = (

let uu____9774 = (FStar_Syntax_Syntax.as_arg e)
in (uu____9774)::[])
in (uu____9754)::uu____9763))
in ((t_with_type1), (uu____9743)))
in FStar_Syntax_Syntax.Tm_app (uu____9726))
in (FStar_Syntax_Syntax.mk uu____9725))
in (uu____9718 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (

let uu____9821 = (

let uu____9828 = (

let uu____9829 = (

let uu____9836 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____9836), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____9829))
in (FStar_Syntax_Syntax.mk uu____9828))
in (uu____9821 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____9851 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____9864) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____9875) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____9851) with
| (eff_name, flags) -> begin
(FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags (fun uu____9896 -> c0))
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____9979 = (

let uu____9986 = (

let uu____9987 = (

let uu____10004 = (

let uu____10015 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____10024 = (

let uu____10035 = (

let uu____10044 = (

let uu____10045 = (

let uu____10046 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____10046)::[])
in (abs uu____10045 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____10044))
in (uu____10035)::[])
in (uu____10015)::uu____10024))
in ((fa), (uu____10004)))
in FStar_Syntax_Syntax.Tm_app (uu____9987))
in (FStar_Syntax_Syntax.mk uu____9986))
in (uu____9979 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____10173 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____10173) with
| true -> begin
f1
end
| uu____10176 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____10192) -> begin
true
end
| uu____10194 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____10241 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____10241), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____10270 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____10270), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____10284 = (

let uu____10285 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10285))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____10284)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10361 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____10364 = (

let uu____10375 = (FStar_Syntax_Syntax.as_arg p)
in (uu____10375)::[])
in (mk_app uu____10361 uu____10364)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____10415 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____10418 = (

let uu____10429 = (FStar_Syntax_Syntax.as_arg p)
in (uu____10429)::[])
in (mk_app uu____10415 uu____10418)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____10464 = (head_and_args t)
in (match (uu____10464) with
| (head1, args) -> begin
(

let head2 = (unascribe head1)
in (

let head3 = (un_uinst head2)
in (

let uu____10513 = (

let uu____10528 = (

let uu____10529 = (FStar_Syntax_Subst.compress head3)
in uu____10529.FStar_Syntax_Syntax.n)
in ((uu____10528), (args)))
in (match (uu____10513) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____10548))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____10614 = (

let uu____10619 = (

let uu____10620 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____10620)::[])
in (FStar_Syntax_Subst.open_term uu____10619 p))
in (match (uu____10614) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____10677 -> begin
(failwith "impossible")
end)
in (

let uu____10685 = (

let uu____10687 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____10687))
in (match (uu____10685) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____10699 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____10703 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10706 -> begin
FStar_Pervasives_Native.None
end))))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____10737 = (head_and_args t)
in (match (uu____10737) with
| (head1, args) -> begin
(

let uu____10788 = (

let uu____10803 = (

let uu____10804 = (FStar_Syntax_Subst.compress head1)
in uu____10804.FStar_Syntax_Syntax.n)
in ((uu____10803), (args)))
in (match (uu____10788) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10826; FStar_Syntax_Syntax.vars = uu____10827}, (u)::[]), ((t1, uu____10830))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____10877 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____10912 = (head_and_args t)
in (match (uu____10912) with
| (head1, args) -> begin
(

let uu____10963 = (

let uu____10978 = (

let uu____10979 = (FStar_Syntax_Subst.compress head1)
in uu____10979.FStar_Syntax_Syntax.n)
in ((uu____10978), (args)))
in (match (uu____10963) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____11001; FStar_Syntax_Syntax.vars = uu____11002}, (u)::[]), ((t1, uu____11005))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____11052 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____11080 = (

let uu____11097 = (unmeta t)
in (head_and_args uu____11097))
in (match (uu____11080) with
| (head1, uu____11100) -> begin
(

let uu____11125 = (

let uu____11126 = (un_uinst head1)
in uu____11126.FStar_Syntax_Syntax.n)
in (match (uu____11125) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____11131 -> begin
false
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____11151 = (

let uu____11164 = (

let uu____11165 = (FStar_Syntax_Subst.compress t)
in uu____11165.FStar_Syntax_Syntax.n)
in (match (uu____11164) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____11295 = (

let uu____11306 = (

let uu____11307 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____11307))
in ((b), (uu____11306)))
in FStar_Pervasives_Native.Some (uu____11295))
end
| uu____11324 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____11151 (fun uu____11362 -> (match (uu____11362) with
| (b, c) -> begin
(

let uu____11399 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____11399) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____11462 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____11499 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____11499)))


type qpats =
FStar_Syntax_Syntax.args Prims.list

type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)


let uu___is_QAll : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
true
end
| uu____11551 -> begin
false
end))


let __proj__QAll__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
_0
end))


let uu___is_QEx : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
true
end
| uu____11594 -> begin
false
end))


let __proj__QEx__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
_0
end))


let uu___is_BaseConn : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
true
end
| uu____11635 -> begin
false
end))


let __proj__BaseConn__item___0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
_0
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective FStar_Pervasives_Native.option = (fun f -> (

let rec unmeta_monadic = (fun f1 -> (

let f2 = (FStar_Syntax_Subst.compress f1)
in (match (f2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____11674)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____11686)) -> begin
(unmeta_monadic t)
end
| uu____11699 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____11795 -> (match (uu____11795) with
| (lid, arity) -> begin
(

let uu____11804 = (

let uu____11821 = (unmeta_monadic f2)
in (head_and_args uu____11821))
in (match (uu____11804) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____11851 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____11851) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____11864 -> begin
FStar_Pervasives_Native.None
end)))
end))
end))
in (FStar_Util.find_map connectives (aux f1)))))
in (

let patterns = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (uu____11910, pats)) -> begin
(

let uu____11948 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____11948)))
end
| uu____11961 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____12008 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____12028 = (head_and_args t1)
in (match (uu____12028) with
| (t2, args) -> begin
(

let uu____12083 = (un_uinst t2)
in (

let uu____12084 = (FStar_All.pipe_right args (FStar_List.map (fun uu____12125 -> (match (uu____12125) with
| (t3, imp) -> begin
(

let uu____12144 = (unascribe t3)
in ((uu____12144), (imp)))
end))))
in ((uu____12083), (uu____12084))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____12195 = (

let uu____12219 = (flat t1)
in ((qopt), (uu____12219)))
in (match (uu____12195) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12259; FStar_Syntax_Syntax.vars = uu____12260}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12263); FStar_Syntax_Syntax.pos = uu____12264; FStar_Syntax_Syntax.vars = uu____12265}, uu____12266))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12368; FStar_Syntax_Syntax.vars = uu____12369}, (uu____12370)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12373); FStar_Syntax_Syntax.pos = uu____12374; FStar_Syntax_Syntax.vars = uu____12375}, uu____12376))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12493; FStar_Syntax_Syntax.vars = uu____12494}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12497); FStar_Syntax_Syntax.pos = uu____12498; FStar_Syntax_Syntax.vars = uu____12499}, uu____12500))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____12593 = (

let uu____12597 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____12597))
in (aux uu____12593 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12607; FStar_Syntax_Syntax.vars = uu____12608}, (uu____12609)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12612); FStar_Syntax_Syntax.pos = uu____12613; FStar_Syntax_Syntax.vars = uu____12614}, uu____12615))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____12724 = (

let uu____12728 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____12728))
in (aux uu____12724 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____12738) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____12791 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____12791) with
| (bs1, t2) -> begin
(

let uu____12800 = (patterns t2)
in (match (uu____12800) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____12848 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____12850 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____12942 = (un_squash t)
in (FStar_Util.bind_opt uu____12942 (fun t1 -> (

let uu____12958 = (head_and_args' t1)
in (match (uu____12958) with
| (hd1, args) -> begin
(

let uu____12997 = (

let uu____13003 = (

let uu____13004 = (un_uinst hd1)
in uu____13004.FStar_Syntax_Syntax.n)
in ((uu____13003), ((FStar_List.length args))))
in (match (uu____12997) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13020) when ((_13020 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_and_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.and_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13023) when ((_13023 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_or_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.or_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13026) when ((_13026 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.c_eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13029) when ((_13029 = (Prims.parse_int "3")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.c_eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13032) when ((_13032 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.c_eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13035) when ((_13035 = (Prims.parse_int "4")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.c_eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13038) when ((_13038 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_true_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.true_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _13041) when ((_13041 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_false_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.false_lid), (args))))
end
| uu____13042 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____13072 = (un_squash t)
in (FStar_Util.bind_opt uu____13072 (fun t1 -> (

let uu____13087 = (arrow_one t1)
in (match (uu____13087) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____13102 = (

let uu____13104 = (is_tot_or_gtot_comp c)
in (not (uu____13104)))
in (match (uu____13102) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13109 -> begin
(

let q = (

let uu____13114 = (comp_to_comp_typ_nouniv c)
in uu____13114.FStar_Syntax_Syntax.result_typ)
in (

let uu____13115 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____13115) with
| true -> begin
(

let uu____13122 = (patterns q)
in (match (uu____13122) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____13183 -> begin
(

let uu____13185 = (

let uu____13186 = (

let uu____13191 = (

let uu____13192 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____13203 = (

let uu____13214 = (FStar_Syntax_Syntax.as_arg q)
in (uu____13214)::[])
in (uu____13192)::uu____13203))
in ((FStar_Parser_Const.imp_lid), (uu____13191)))
in BaseConn (uu____13186))
in FStar_Pervasives_Native.Some (uu____13185))
end)))
end))
end
| uu____13247 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____13255 = (un_squash t)
in (FStar_Util.bind_opt uu____13255 (fun t1 -> (

let uu____13286 = (head_and_args' t1)
in (match (uu____13286) with
| (hd1, args) -> begin
(

let uu____13325 = (

let uu____13340 = (

let uu____13341 = (un_uinst hd1)
in uu____13341.FStar_Syntax_Syntax.n)
in ((uu____13340), (args)))
in (match (uu____13325) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____13358))::((a2, uu____13360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____13411 = (

let uu____13412 = (FStar_Syntax_Subst.compress a2)
in uu____13412.FStar_Syntax_Syntax.n)
in (match (uu____13411) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____13419) -> begin
(

let uu____13454 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____13454) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____13507 -> begin
(failwith "impossible")
end)
in (

let uu____13515 = (patterns q1)
in (match (uu____13515) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____13576 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____13577 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____13600 = (destruct_sq_forall phi)
in (match (uu____13600) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _13610 -> FStar_Pervasives_Native.Some (_13610)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____13617 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____13623 = (destruct_sq_exists phi)
in (match (uu____13623) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _13633 -> FStar_Pervasives_Native.Some (_13633)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____13640 -> begin
f1
end))
end
| uu____13643 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____13647 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____13647 (fun uu____13652 -> (

let uu____13653 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____13653 (fun uu____13658 -> (

let uu____13659 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____13659 (fun uu____13664 -> (

let uu____13665 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____13665 (fun uu____13670 -> (

let uu____13671 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____13671 (fun uu____13675 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____13693 = (

let uu____13698 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____13698))
in (

let uu____13699 = (

let uu____13700 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____13700))
in (

let uu____13703 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____13693 a.FStar_Syntax_Syntax.action_univs uu____13699 FStar_Parser_Const.effect_Tot_lid uu____13703 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____13729 = (

let uu____13736 = (

let uu____13737 = (

let uu____13754 = (

let uu____13765 = (FStar_Syntax_Syntax.as_arg t)
in (uu____13765)::[])
in ((reify_1), (uu____13754)))
in FStar_Syntax_Syntax.Tm_app (uu____13737))
in (FStar_Syntax_Syntax.mk uu____13736))
in (uu____13729 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let mk_reflect : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reflect_ = (

let uu____13817 = (

let uu____13824 = (

let uu____13825 = (

let uu____13826 = (FStar_Ident.lid_of_str "Bogus.Effect")
in FStar_Const.Const_reflect (uu____13826))
in FStar_Syntax_Syntax.Tm_constant (uu____13825))
in (FStar_Syntax_Syntax.mk uu____13824))
in (uu____13817 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____13828 = (

let uu____13835 = (

let uu____13836 = (

let uu____13853 = (

let uu____13864 = (FStar_Syntax_Syntax.as_arg t)
in (uu____13864)::[])
in ((reflect_), (uu____13853)))
in FStar_Syntax_Syntax.Tm_app (uu____13836))
in (FStar_Syntax_Syntax.mk uu____13835))
in (uu____13828 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____13908) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____13933 = (unfold_lazy i)
in (delta_qualifier uu____13933))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____13935) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____13936) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____13937) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____13960) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____13973) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____13974) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____13981) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____13982) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____13998) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____14003; FStar_Syntax_Syntax.index = uu____14004; FStar_Syntax_Syntax.sort = t2}, uu____14006) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____14015) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____14021, uu____14022) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____14064) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____14089, t2, uu____14091) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____14116, t2) -> begin
(delta_qualifier t2)
end)))


let rec incr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_constant_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_constant_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_equational_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d1) -> begin
(incr_delta_depth d1)
end))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let uu____14155 = (delta_qualifier t)
in (incr_delta_depth uu____14155)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____14163 = (

let uu____14164 = (FStar_Syntax_Subst.compress t)
in uu____14164.FStar_Syntax_Syntax.n)
in (match (uu____14163) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____14169 -> begin
false
end)))


let rec apply_last : 'Auu____14178 . ('Auu____14178  ->  'Auu____14178)  ->  'Auu____14178 Prims.list  ->  'Auu____14178 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____14204 = (f a)
in (uu____14204)::[])
end
| (x)::xs -> begin
(

let uu____14209 = (apply_last f xs)
in (x)::uu____14209)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____14264 = (

let uu____14271 = (

let uu____14272 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____14272))
in (FStar_Syntax_Syntax.mk uu____14271))
in (uu____14264 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____14286 = (

let uu____14291 = (

let uu____14292 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____14292 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____14291 args))
in (uu____14286 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____14306 = (

let uu____14311 = (

let uu____14312 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____14312 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____14311 args))
in (uu____14306 FStar_Pervasives_Native.None pos)))
in (

let uu____14313 = (

let uu____14314 = (

let uu____14315 = (FStar_Syntax_Syntax.iarg typ)
in (uu____14315)::[])
in (nil uu____14314 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____14349 = (

let uu____14350 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____14359 = (

let uu____14370 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____14379 = (

let uu____14390 = (FStar_Syntax_Syntax.as_arg a)
in (uu____14390)::[])
in (uu____14370)::uu____14379))
in (uu____14350)::uu____14359))
in (cons1 uu____14349 t.FStar_Syntax_Syntax.pos))) l uu____14313))))))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____14499 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____14613 -> begin
false
end))


let eqprod : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a * 'b)  ->  ('a * 'b)  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| ((x1, x2), (y1, y2)) -> begin
((e1 x1 y1) && (e2 x2 y2))
end))


let eqopt : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a FStar_Pervasives_Native.option  ->  'a FStar_Pervasives_Native.option  ->  Prims.bool = (fun e x y -> (match (((x), (y))) with
| (FStar_Pervasives_Native.Some (x1), FStar_Pervasives_Native.Some (y1)) -> begin
(e x1 y1)
end
| uu____14779 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____14814 -> begin
((

let uu____14817 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____14817) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____14842 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____15039 = (unmeta_safe t1)
in (canon_app uu____15039))
in (

let t21 = (

let uu____15045 = (unmeta_safe t2)
in (canon_app uu____15045))
in (

let uu____15048 = (

let uu____15053 = (

let uu____15054 = (

let uu____15057 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____15057))
in uu____15054.FStar_Syntax_Syntax.n)
in (

let uu____15058 = (

let uu____15059 = (

let uu____15062 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____15062))
in uu____15059.FStar_Syntax_Syntax.n)
in ((uu____15053), (uu____15058))))
in (match (uu____15048) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____15064), uu____15065) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15074, FStar_Syntax_Syntax.Tm_uinst (uu____15075)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____15084), uu____15085) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15110, FStar_Syntax_Syntax.Tm_delayed (uu____15111)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____15136), uu____15137) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15166, FStar_Syntax_Syntax.Tm_ascribed (uu____15167)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_bvar (x), FStar_Syntax_Syntax.Tm_bvar (y)) -> begin
(check "bvar" (Prims.op_Equality x.FStar_Syntax_Syntax.index y.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(check "name" (Prims.op_Equality x.FStar_Syntax_Syntax.index y.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_fvar (x), FStar_Syntax_Syntax.Tm_fvar (y)) -> begin
(

let uu____15206 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____15206))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____15211 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____15211))
end
| (FStar_Syntax_Syntax.Tm_type (uu____15214), FStar_Syntax_Syntax.Tm_type (uu____15215)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____15273 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____15273)) && (

let uu____15283 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____15283)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____15332 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____15332)) && (

let uu____15342 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____15342)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((

let uu____15359 = (term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort b2.FStar_Syntax_Syntax.sort)
in (check "refine bv sort" uu____15359)) && (

let uu____15363 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____15363)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____15420 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____15420)) && (

let uu____15424 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____15424)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____15513 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____15513)) && (

let uu____15517 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____15517)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____15534), uu____15535) -> begin
(

let uu____15536 = (

let uu____15538 = (unlazy t11)
in (term_eq_dbg dbg uu____15538 t21))
in (check "lazy_l" uu____15536))
end
| (uu____15540, FStar_Syntax_Syntax.Tm_lazy (uu____15541)) -> begin
(

let uu____15542 = (

let uu____15544 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____15544))
in (check "lazy_r" uu____15542))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____15589 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____15589))) && (

let uu____15593 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____15593)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____15597), FStar_Syntax_Syntax.Tm_uvar (u2, uu____15599)) -> begin
(check "uvar" (Prims.op_Equality u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((

let uu____15657 = (

let uu____15659 = (eq_quoteinfo qi1 qi2)
in (Prims.op_Equality uu____15659 Equal))
in (check "tm_quoted qi" uu____15657)) && (

let uu____15662 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____15662)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____15692 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____15692)) && (

let uu____15696 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____15696)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____15715 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____15715)) && (

let uu____15719 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____15719))) && (

let uu____15723 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____15723)))
end
| uu____15726 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____15732) -> begin
(fail "unk")
end
| (uu____15734, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____15736), uu____15737) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____15739), uu____15740) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____15742), uu____15743) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____15745), uu____15746) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____15748), uu____15749) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____15751), uu____15752) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____15772), uu____15773) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____15789), uu____15790) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____15798), uu____15799) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____15817), uu____15818) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____15842), uu____15843) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15858), uu____15859) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____15873), uu____15874) -> begin
(fail "bottom")
end
| (uu____15882, FStar_Syntax_Syntax.Tm_bvar (uu____15883)) -> begin
(fail "bottom")
end
| (uu____15885, FStar_Syntax_Syntax.Tm_name (uu____15886)) -> begin
(fail "bottom")
end
| (uu____15888, FStar_Syntax_Syntax.Tm_fvar (uu____15889)) -> begin
(fail "bottom")
end
| (uu____15891, FStar_Syntax_Syntax.Tm_constant (uu____15892)) -> begin
(fail "bottom")
end
| (uu____15894, FStar_Syntax_Syntax.Tm_type (uu____15895)) -> begin
(fail "bottom")
end
| (uu____15897, FStar_Syntax_Syntax.Tm_abs (uu____15898)) -> begin
(fail "bottom")
end
| (uu____15918, FStar_Syntax_Syntax.Tm_arrow (uu____15919)) -> begin
(fail "bottom")
end
| (uu____15935, FStar_Syntax_Syntax.Tm_refine (uu____15936)) -> begin
(fail "bottom")
end
| (uu____15944, FStar_Syntax_Syntax.Tm_app (uu____15945)) -> begin
(fail "bottom")
end
| (uu____15963, FStar_Syntax_Syntax.Tm_match (uu____15964)) -> begin
(fail "bottom")
end
| (uu____15988, FStar_Syntax_Syntax.Tm_let (uu____15989)) -> begin
(fail "bottom")
end
| (uu____16004, FStar_Syntax_Syntax.Tm_uvar (uu____16005)) -> begin
(fail "bottom")
end
| (uu____16019, FStar_Syntax_Syntax.Tm_meta (uu____16020)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____16055 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____16055))) (fun q1 q2 -> (

let uu____16067 = (

let uu____16069 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____16069 Equal))
in (check "arg qual" uu____16067))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____16094 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____16094))) (fun q1 q2 -> (

let uu____16106 = (

let uu____16108 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____16108 Equal))
in (check "binder qual" uu____16106))) b1 b2))
and lcomp_eq_dbg : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> (fail "lcomp"))
and residual_eq_dbg : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> (fail "residual"))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____16128 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____16128)) && (

let uu____16132 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____16132))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflag  ->  FStar_Syntax_Syntax.cflag  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____16142 uu____16143 -> (match (((uu____16142), (uu____16143))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____16270 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____16270)) && (

let uu____16274 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____16274))) && (

let uu____16278 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____16320 -> begin
false
end)
in (check "branch when" uu____16278)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____16341 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____16341)) && (

let uu____16350 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____16350))) && (

let uu____16354 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____16354))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____16371 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____16371 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____16425) -> begin
(

let uu____16448 = (

let uu____16450 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____16450))
in ((Prims.parse_int "1") + uu____16448))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____16453 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____16453))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____16457 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____16457))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____16466 = (sizeof t1)
in ((FStar_List.length us) + uu____16466))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____16470) -> begin
(

let uu____16495 = (sizeof t1)
in (

let uu____16497 = (FStar_List.fold_left (fun acc uu____16512 -> (match (uu____16512) with
| (bv, uu____16522) -> begin
(

let uu____16527 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____16527))
end)) (Prims.parse_int "0") bs)
in (uu____16495 + uu____16497)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____16556 = (sizeof hd1)
in (

let uu____16558 = (FStar_List.fold_left (fun acc uu____16573 -> (match (uu____16573) with
| (arg, uu____16583) -> begin
(

let uu____16588 = (sizeof arg)
in (acc + uu____16588))
end)) (Prims.parse_int "0") args)
in (uu____16556 + uu____16558)))
end
| uu____16591 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____16605 = (

let uu____16606 = (un_uinst t)
in uu____16606.FStar_Syntax_Syntax.n)
in (match (uu____16605) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____16611 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun t s -> (

let uu____16660 = (FStar_Options.set_options t s)
in (match (uu____16660) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ("Failed to process pragma: use \'fstar --help\' to see which options are available")) r)
end
| FStar_Getopt.Error (s1) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ((Prims.op_Hat "Failed to process pragma: " s1))) r)
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
(match ((Prims.op_Equality p FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____16668 -> begin
()
end)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 FStar_Options.Set o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____16677 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____16677 (fun a1 -> ())));
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
)
end
| FStar_Syntax_Syntax.PushOptions (sopt) -> begin
((FStar_Options.internal_push ());
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
)
end
| FStar_Syntax_Syntax.PopOptions -> begin
(

let uu____16692 = (FStar_Options.internal_pop ())
in (match (uu____16692) with
| true -> begin
()
end
| uu____16695 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ("Cannot #pop-options, stack would become empty")) r)
end))
end)))


let rec unbound_variables : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun tm -> (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____16724) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____16751) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____16766) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____16767) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____16768) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____16777) -> begin
(

let uu____16802 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____16802) with
| (bs1, t2) -> begin
(

let uu____16811 = (FStar_List.collect (fun uu____16823 -> (match (uu____16823) with
| (b, uu____16833) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____16838 = (unbound_variables t2)
in (FStar_List.append uu____16811 uu____16838)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____16863 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____16863) with
| (bs1, c1) -> begin
(

let uu____16872 = (FStar_List.collect (fun uu____16884 -> (match (uu____16884) with
| (b, uu____16894) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____16899 = (unbound_variables_comp c1)
in (FStar_List.append uu____16872 uu____16899)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____16908 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____16908) with
| (bs, t2) -> begin
(

let uu____16931 = (FStar_List.collect (fun uu____16943 -> (match (uu____16943) with
| (b1, uu____16953) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____16958 = (unbound_variables t2)
in (FStar_List.append uu____16931 uu____16958)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____16987 = (FStar_List.collect (fun uu____17001 -> (match (uu____17001) with
| (x, uu____17013) -> begin
(unbound_variables x)
end)) args)
in (

let uu____17022 = (unbound_variables t1)
in (FStar_List.append uu____16987 uu____17022)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____17063 = (unbound_variables t1)
in (

let uu____17066 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____17081 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____17081) with
| (p, wopt, t2) -> begin
(

let uu____17103 = (unbound_variables t2)
in (

let uu____17106 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____17103 uu____17106)))
end)))))
in (FStar_List.append uu____17063 uu____17066)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____17120) -> begin
(

let uu____17161 = (unbound_variables t1)
in (

let uu____17164 = (

let uu____17167 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____17198 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____17167 uu____17198)))
in (FStar_List.append uu____17161 uu____17164)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____17239 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____17242 = (

let uu____17245 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____17248 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____17253) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____17255 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____17255) with
| (uu____17276, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____17245 uu____17248)))
in (FStar_List.append uu____17239 uu____17242)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____17278, lbs), t1) -> begin
(

let uu____17298 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____17298) with
| (lbs1, t2) -> begin
(

let uu____17313 = (unbound_variables t2)
in (

let uu____17316 = (FStar_List.collect (fun lb -> (

let uu____17323 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____17326 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____17323 uu____17326)))) lbs1)
in (FStar_List.append uu____17313 uu____17316)))
end))
end
| FStar_Syntax_Syntax.Tm_quoted (tm1, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
[]
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(unbound_variables tm1)
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____17343 = (unbound_variables t1)
in (

let uu____17346 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____17351, args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____17406 -> (match (uu____17406) with
| (a, uu____17418) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____17427, uu____17428, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____17434, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____17440) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____17449) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____17450) -> begin
[]
end)
in (FStar_List.append uu____17343 uu____17346)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____17457) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____17467) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____17477 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____17480 = (FStar_List.collect (fun uu____17494 -> (match (uu____17494) with
| (a, uu____17506) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____17477 uu____17480)))
end))


let extract_attr' : FStar_Ident.lid  ->  FStar_Syntax_Syntax.term Prims.list  ->  (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args) FStar_Pervasives_Native.option = (fun attr_lid attrs -> (

let rec aux = (fun acc attrs1 -> (match (attrs1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (h)::t -> begin
(

let uu____17621 = (head_and_args h)
in (match (uu____17621) with
| (head1, args) -> begin
(

let uu____17682 = (

let uu____17683 = (FStar_Syntax_Subst.compress head1)
in uu____17683.FStar_Syntax_Syntax.n)
in (match (uu____17682) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv attr_lid) -> begin
(

let attrs' = (FStar_List.rev_acc acc t)
in FStar_Pervasives_Native.Some (((attrs'), (args))))
end
| uu____17736 -> begin
(aux ((h)::acc) t)
end))
end))
end))
in (aux [] attrs)))


let extract_attr : FStar_Ident.lid  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args) FStar_Pervasives_Native.option = (fun attr_lid se -> (

let uu____17760 = (extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____17760) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (attrs', t) -> begin
FStar_Pervasives_Native.Some ((((

let uu___2540_17802 = se
in {FStar_Syntax_Syntax.sigel = uu___2540_17802.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___2540_17802.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___2540_17802.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___2540_17802.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs'})), (t)))
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____17810 = (

let uu____17811 = (FStar_Syntax_Subst.compress t)
in uu____17811.FStar_Syntax_Syntax.n)
in (match (uu____17810) with
| FStar_Syntax_Syntax.Tm_arrow (uu____17815, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____17843))::uu____17844 -> begin
(

let pats' = (unmeta pats)
in (

let uu____17904 = (head_and_args pats')
in (match (uu____17904) with
| (head1, uu____17923) -> begin
(

let uu____17948 = (

let uu____17949 = (un_uinst head1)
in uu____17949.FStar_Syntax_Syntax.n)
in (match (uu____17948) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____17954 -> begin
false
end))
end)))
end
| uu____17956 -> begin
false
end)
end
| uu____17968 -> begin
false
end)
end
| uu____17970 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____17986 = (

let uu____18003 = (unmeta e)
in (head_and_args uu____18003))
in (match (uu____17986) with
| (head1, args) -> begin
(

let uu____18034 = (

let uu____18049 = (

let uu____18050 = (un_uinst head1)
in uu____18050.FStar_Syntax_Syntax.n)
in ((uu____18049), (args)))
in (match (uu____18034) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____18068) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____18092)::((hd1, uu____18094))::((tl1, uu____18096))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____18163 = (

let uu____18166 = (

let uu____18169 = (list_elements tl1)
in (FStar_Util.must uu____18169))
in (hd1)::uu____18166)
in FStar_Pervasives_Native.Some (uu____18163))
end
| uu____18178 -> begin
FStar_Pervasives_Native.None
end))
end)))


let unthunk_lemma_post : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____18207 = (

let uu____18208 = (FStar_Syntax_Subst.compress t)
in uu____18208.FStar_Syntax_Syntax.n)
in (match (uu____18207) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____18215) -> begin
(

let uu____18250 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____18250) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____18284 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____18284) with
| true -> begin
(

let uu____18291 = (

let uu____18302 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____18302)::[])
in (mk_app t uu____18291))
end
| uu____18327 -> begin
e1
end)))
end))
end
| uu____18329 -> begin
(

let uu____18330 = (

let uu____18341 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____18341)::[])
in (mk_app t uu____18330))
end)))


let smt_lemma_as_forall : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universe Prims.list)  ->  FStar_Syntax_Syntax.term = (fun t universe_of_binders -> (

let list_elements1 = (fun e -> (

let uu____18396 = (list_elements e)
in (match (uu____18396) with
| FStar_Pervasives_Native.Some (l) -> begin
l
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_NonListLiteralSMTPattern), ("SMT pattern is not a list literal; ignoring the pattern")));
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____18427 = (

let uu____18444 = (unmeta p)
in (FStar_All.pipe_right uu____18444 head_and_args))
in (match (uu____18427) with
| (head1, args) -> begin
(

let uu____18495 = (

let uu____18510 = (

let uu____18511 = (un_uinst head1)
in uu____18511.FStar_Syntax_Syntax.n)
in ((uu____18510), (args)))
in (match (uu____18495) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____18533, uu____18534))::(arg)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
arg
end
| uu____18586 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____18641 = (

let uu____18658 = (unmeta t1)
in (FStar_All.pipe_right uu____18658 head_and_args))
in (match (uu____18641) with
| (head1, args) -> begin
(

let uu____18705 = (

let uu____18720 = (

let uu____18721 = (un_uinst head1)
in uu____18721.FStar_Syntax_Syntax.n)
in ((uu____18720), (args)))
in (match (uu____18705) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____18740))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____18777 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____18807 = (smt_pat_or1 t1)
in (match (uu____18807) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____18829 = (list_elements1 e)
in (FStar_All.pipe_right uu____18829 (FStar_List.map (fun branch1 -> (

let uu____18859 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____18859 (FStar_List.map one_pat)))))))
end
| uu____18882 -> begin
(

let uu____18887 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____18887)::[])
end))
end
| uu____18938 -> begin
(

let uu____18941 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____18941)::[])
end))))
in (

let uu____18992 = (

let uu____19025 = (

let uu____19026 = (FStar_Syntax_Subst.compress t)
in uu____19026.FStar_Syntax_Syntax.n)
in (match (uu____19025) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____19083 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____19083) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____19154; FStar_Syntax_Syntax.effect_name = uu____19155; FStar_Syntax_Syntax.result_typ = uu____19156; FStar_Syntax_Syntax.effect_args = ((pre, uu____19158))::((post, uu____19160))::((pats, uu____19162))::[]; FStar_Syntax_Syntax.flags = uu____19163}) -> begin
(

let uu____19224 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____19224)))
end
| uu____19261 -> begin
(failwith "impos")
end)
end))
end
| uu____19295 -> begin
(failwith "Impos")
end))
in (match (uu____18992) with
| (binders, pre, post, patterns) -> begin
(

let post1 = (unthunk_lemma_post post)
in (

let body = (

let uu____19387 = (

let uu____19394 = (

let uu____19395 = (

let uu____19402 = (mk_imp pre post1)
in (

let uu____19405 = (

let uu____19406 = (

let uu____19427 = (FStar_Syntax_Syntax.binders_to_names binders)
in ((uu____19427), (patterns)))
in FStar_Syntax_Syntax.Meta_pattern (uu____19406))
in ((uu____19402), (uu____19405))))
in FStar_Syntax_Syntax.Tm_meta (uu____19395))
in (FStar_Syntax_Syntax.mk uu____19394))
in (uu____19387 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let quant = (

let uu____19451 = (universe_of_binders binders)
in (FStar_List.fold_right2 (fun b u out -> (mk_forall u (FStar_Pervasives_Native.fst b) out)) binders uu____19451 body))
in quant)))
end))))))




