
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

let uu___225_1559 = c
in (

let uu____1560 = (

let uu____1561 = (

let uu___227_1562 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___227_1562.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___227_1562.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___227_1562.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___227_1562.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1561))
in {FStar_Syntax_Syntax.n = uu____1560; FStar_Syntax_Syntax.pos = uu___225_1559.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___225_1559.FStar_Syntax_Syntax.vars})))


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
| uu____1602 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, uu____1624))::[] -> begin
wp
end
| uu____1649 -> begin
(

let uu____1660 = (

let uu____1662 = (

let uu____1664 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args FStar_List.length)
in (FStar_All.pipe_right uu____1664 FStar_Util.string_of_int))
in (FStar_Util.format2 "Impossible: Got a computation %s with %s effect args" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str uu____1662))
in (failwith uu____1660))
end)
in (

let uu____1688 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((uu____1688), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1702) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1712) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___0_1737 -> (match (uu___0_1737) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1741 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___1_1758 -> (match (uu___1_1758) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1762 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1794) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1804) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___2_1819 -> (match (uu___2_1819) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1822 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_or_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> ((is_pure_effect l) || (is_ghost_effect l)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1863 = (

let uu____1864 = (FStar_Syntax_Subst.compress t)
in uu____1864.FStar_Syntax_Syntax.n)
in (match (uu____1863) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1868, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1890 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1905 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1914 = (

let uu____1915 = (FStar_Syntax_Subst.compress t)
in uu____1915.FStar_Syntax_Syntax.n)
in (match (uu____1914) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1919, c) -> begin
(is_lemma_comp c)
end
| uu____1941 -> begin
false
end)))


let rec head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1949 = (

let uu____1950 = (FStar_Syntax_Subst.compress t)
in uu____1950.FStar_Syntax_Syntax.n)
in (match (uu____1949) with
| FStar_Syntax_Syntax.Tm_app (t1, uu____1954) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_match (t1, uu____1980) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_abs (uu____2017, t1, uu____2019) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2045, uu____2046) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____2088) -> begin
(head_of t1)
end
| uu____2093 -> begin
t
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____2171 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____2253 = (head_and_args' head1)
in (match (uu____2253) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____2322 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2349) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____2354 -> begin
t1
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___3_2372 -> (match (uu___3_2372) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2375 -> begin
false
end)))))
end
| uu____2377 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____2394) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____2404) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2433) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____2442) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___366_2454 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___366_2454.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___366_2454.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___366_2454.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___366_2454.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___4_2470 -> (match (uu___4_2470) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2474 -> begin
false
end)))))


let comp_effect_args : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.args = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2482) -> begin
[]
end
| FStar_Syntax_Syntax.GTotal (uu____2499) -> begin
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
| uu____2543 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2553, uu____2554) -> begin
(unascribe e2)
end
| uu____2595 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2648, uu____2649) -> begin
(ascribe t' k)
end
| uu____2690 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2717 = (

let uu____2726 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2726))
in (uu____2717 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2782 = (

let uu____2783 = (FStar_Syntax_Subst.compress t)
in uu____2783.FStar_Syntax_Syntax.n)
in (match (uu____2782) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2787 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2787))
end
| uu____2788 -> begin
t
end)))


let unlazy_emb : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2795 = (

let uu____2796 = (FStar_Syntax_Subst.compress t)
in uu____2796.FStar_Syntax_Syntax.n)
in (match (uu____2795) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(match (i.FStar_Syntax_Syntax.lkind) with
| FStar_Syntax_Syntax.Lazy_embedding (uu____2800) -> begin
(

let uu____2809 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2809))
end
| uu____2810 -> begin
t
end)
end
| uu____2811 -> begin
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
| (FStar_Syntax_Syntax.Lazy_optionstate, FStar_Syntax_Syntax.Lazy_optionstate) -> begin
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
| uu____2836 -> begin
false
end))


let unlazy_as_t : 'Auu____2849 . FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.term  ->  'Auu____2849 = (fun k t -> (

let uu____2860 = (

let uu____2861 = (FStar_Syntax_Subst.compress t)
in uu____2861.FStar_Syntax_Syntax.n)
in (match (uu____2860) with
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k'; FStar_Syntax_Syntax.ltyp = uu____2866; FStar_Syntax_Syntax.rng = uu____2867}) when (eq_lazy_kind k k') -> begin
(FStar_Dyn.undyn v1)
end
| uu____2870 -> begin
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

let uu____2911 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2911; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.ltyp = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2924 = (

let uu____2939 = (unascribe t)
in (head_and_args' uu____2939))
in (match (uu____2924) with
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
| uu____2973 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____2984 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____2995 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let eq_inj : eq_result  ->  eq_result  ->  eq_result = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____3045) -> begin
NotEqual
end
| (uu____3046, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____3047) -> begin
Unknown
end
| (uu____3048, Unknown) -> begin
Unknown
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___5_3157 -> (match (uu___5_3157) with
| true -> begin
Equal
end
| uu____3160 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___6_3168 -> (match (uu___6_3168) with
| true -> begin
Equal
end
| uu____3171 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____3189 -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____3211 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____3211) with
| true -> begin
(

let uu____3215 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____3292 -> (match (uu____3292) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____3333 = (eq_tm a1 a2)
in (eq_inj acc uu____3333))
end)) Equal) uu____3215))
end
| uu____3334 -> begin
NotEqual
end)))
in (

let heads_and_args_in_case_both_data = (

let uu____3347 = (

let uu____3364 = (FStar_All.pipe_right t11 unmeta)
in (FStar_All.pipe_right uu____3364 head_and_args))
in (match (uu____3347) with
| (head1, args1) -> begin
(

let uu____3417 = (

let uu____3434 = (FStar_All.pipe_right t21 unmeta)
in (FStar_All.pipe_right uu____3434 head_and_args))
in (match (uu____3417) with
| (head2, args2) -> begin
(

let uu____3487 = (

let uu____3492 = (

let uu____3493 = (un_uinst head1)
in uu____3493.FStar_Syntax_Syntax.n)
in (

let uu____3496 = (

let uu____3497 = (un_uinst head2)
in uu____3497.FStar_Syntax_Syntax.n)
in ((uu____3492), (uu____3496))))
in (match (uu____3487) with
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) when ((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
FStar_Pervasives_Native.Some (((f), (args1), (g), (args2)))
end
| uu____3524 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
in (

let uu____3537 = (

let uu____3542 = (

let uu____3543 = (unmeta t11)
in uu____3543.FStar_Syntax_Syntax.n)
in (

let uu____3546 = (

let uu____3547 = (unmeta t21)
in uu____3547.FStar_Syntax_Syntax.n)
in ((uu____3542), (uu____3546))))
in (match (uu____3537) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____3553), uu____3554) -> begin
(

let uu____3555 = (unlazy t11)
in (eq_tm uu____3555 t21))
end
| (uu____3556, FStar_Syntax_Syntax.Tm_lazy (uu____3557)) -> begin
(

let uu____3558 = (unlazy t21)
in (eq_tm t11 uu____3558))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| uu____3561 when (FStar_All.pipe_right heads_and_args_in_case_both_data FStar_Util.is_some) -> begin
(

let uu____3585 = (FStar_All.pipe_right heads_and_args_in_case_both_data FStar_Util.must)
in (FStar_All.pipe_right uu____3585 (fun uu____3633 -> (match (uu____3633) with
| (f, args1, g, args2) -> begin
(equal_data f args1 g args2)
end))))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____3648 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____3648))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____3662 = (eq_tm f g)
in (eq_and uu____3662 (fun uu____3665 -> (

let uu____3666 = (eq_univs_list us vs)
in (equal_if uu____3666)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3668)), uu____3669) -> begin
Unknown
end
| (uu____3670, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3671))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____3674 = (FStar_Const.eq_const c d)
in (equal_iff uu____3674))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu____3677)), FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu____3679))) -> begin
(

let uu____3708 = (FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head)
in (equal_if uu____3708))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____3762 = (

let uu____3767 = (

let uu____3768 = (un_uinst h1)
in uu____3768.FStar_Syntax_Syntax.n)
in (

let uu____3771 = (

let uu____3772 = (un_uinst h2)
in uu____3772.FStar_Syntax_Syntax.n)
in ((uu____3767), (uu____3771))))
in (match (uu____3762) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____3778 = (

let uu____3780 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____3780))
in (FStar_List.mem uu____3778 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____3782 -> begin
(

let uu____3787 = (eq_tm h1 h2)
in (eq_and uu____3787 (fun uu____3789 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____3895 = (FStar_List.zip bs1 bs2)
in (

let uu____3958 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____3995 a -> (match (uu____3995) with
| (b1, b2) -> begin
(eq_and a (fun uu____4088 -> (branch_matches b1 b2)))
end)) uu____3895 uu____3958)))
end
| uu____4089 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____4093 = (eq_univs u v1)
in (equal_if uu____4093))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(

let uu____4107 = (eq_quoteinfo q1 q2)
in (eq_and uu____4107 (fun uu____4109 -> (eq_tm t12 t22))))
end
| (FStar_Syntax_Syntax.Tm_refine (t12, phi1), FStar_Syntax_Syntax.Tm_refine (t22, phi2)) -> begin
(

let uu____4122 = (eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort)
in (eq_and uu____4122 (fun uu____4124 -> (eq_tm phi1 phi2))))
end
| uu____4125 -> begin
Unknown
end))))))))))
and eq_quoteinfo : FStar_Syntax_Syntax.quoteinfo  ->  FStar_Syntax_Syntax.quoteinfo  ->  eq_result = (fun q1 q2 -> (match ((Prims.op_disEquality q1.FStar_Syntax_Syntax.qkind q2.FStar_Syntax_Syntax.qkind)) with
| true -> begin
NotEqual
end
| uu____4133 -> begin
(eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes q2.FStar_Syntax_Syntax.antiquotes)
end))
and eq_antiquotes : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| ([], uu____4197) -> begin
NotEqual
end
| (uu____4228, []) -> begin
NotEqual
end
| (((x1, t1))::a11, ((x2, t2))::a21) -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x1 x2)))) with
| true -> begin
NotEqual
end
| uu____4318 -> begin
(

let uu____4320 = (eq_tm t1 t2)
in (match (uu____4320) with
| NotEqual -> begin
NotEqual
end
| Unknown -> begin
(

let uu____4321 = (eq_antiquotes a11 a21)
in (match (uu____4321) with
| NotEqual -> begin
NotEqual
end
| uu____4322 -> begin
Unknown
end))
end
| Equal -> begin
(eq_antiquotes a11 a21)
end))
end)
end))
and branch_matches : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  eq_result = (fun b1 b2 -> (

let related_by = (fun f o1 o2 -> (match (((o1), (o2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(f x y)
end
| (uu____4406, uu____4407) -> begin
false
end))
in (

let uu____4417 = b1
in (match (uu____4417) with
| (p1, w1, t1) -> begin
(

let uu____4451 = b2
in (match (uu____4451) with
| (p2, w2, t2) -> begin
(

let uu____4485 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____4485) with
| true -> begin
(

let uu____4488 = ((

let uu____4492 = (eq_tm t1 t2)
in (Prims.op_Equality uu____4492 Equal)) && (related_by (fun t11 t21 -> (

let uu____4501 = (eq_tm t11 t21)
in (Prims.op_Equality uu____4501 Equal))) w1 w2))
in (match (uu____4488) with
| true -> begin
Equal
end
| uu____4503 -> begin
Unknown
end))
end
| uu____4505 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____4566))::a11, ((b, uu____4569))::b1) -> begin
(

let uu____4643 = (eq_tm a b)
in (match (uu____4643) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____4644 -> begin
Unknown
end))
end
| uu____4645 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let eq_aqual : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
Equal
end
| (FStar_Pervasives_Native.None, uu____4700) -> begin
NotEqual
end
| (uu____4707, FStar_Pervasives_Native.None) -> begin
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
| uu____4737 -> begin
NotEqual
end))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____4754) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4760, uu____4761) -> begin
(unrefine t2)
end
| uu____4802 -> begin
t1
end)))


let rec is_uvar : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4810 = (

let uu____4811 = (FStar_Syntax_Subst.compress t)
in uu____4811.FStar_Syntax_Syntax.n)
in (match (uu____4810) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4815) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4830) -> begin
(is_uvar t1)
end
| FStar_Syntax_Syntax.Tm_app (uu____4835) -> begin
(

let uu____4852 = (

let uu____4853 = (FStar_All.pipe_right t head_and_args)
in (FStar_All.pipe_right uu____4853 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4852 is_uvar))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4916, uu____4917) -> begin
(is_uvar t1)
end
| uu____4958 -> begin
false
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4967 = (

let uu____4968 = (unrefine t)
in uu____4968.FStar_Syntax_Syntax.n)
in (match (uu____4967) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____4974) -> begin
(is_unit head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5000) -> begin
(is_unit t1)
end
| uu____5005 -> begin
false
end)))


let is_eqtype_no_unrefine : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5014 = (

let uu____5015 = (FStar_Syntax_Subst.compress t)
in uu____5015.FStar_Syntax_Syntax.n)
in (match (uu____5014) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid)
end
| uu____5020 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____5029 = (

let uu____5030 = (FStar_Syntax_Subst.compress e)
in uu____5030.FStar_Syntax_Syntax.n)
in (match (uu____5029) with
| FStar_Syntax_Syntax.Tm_abs (uu____5034) -> begin
true
end
| uu____5054 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5063 = (

let uu____5064 = (FStar_Syntax_Subst.compress t)
in uu____5064.FStar_Syntax_Syntax.n)
in (match (uu____5063) with
| FStar_Syntax_Syntax.Tm_arrow (uu____5068) -> begin
true
end
| uu____5084 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____5094) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5100, uu____5101) -> begin
(pre_typ t2)
end
| uu____5142 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____5167 = (

let uu____5168 = (un_uinst typ1)
in uu____5168.FStar_Syntax_Syntax.n)
in (match (uu____5167) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____5233 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____5263 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____5284, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____5291) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____5296, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5307, uu____5308, uu____5309, uu____5310, uu____5311) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____5321, uu____5322, uu____5323, uu____5324) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____5330, uu____5331, uu____5332, uu____5333, uu____5334) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5342, uu____5343) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____5345, uu____5346) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____5348) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____5349) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____5350) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____5364 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___7_5390 -> (match (uu___7_5390) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____5404 'Auu____5405 . ('Auu____5404 FStar_Syntax_Syntax.syntax * 'Auu____5405)  ->  FStar_Range.range = (fun uu____5416 -> (match (uu____5416) with
| (hd1, uu____5424) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____5438 'Auu____5439 . ('Auu____5438 FStar_Syntax_Syntax.syntax * 'Auu____5439) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____5537 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_app_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f bs -> (

let uu____5596 = (FStar_List.map (fun uu____5623 -> (match (uu____5623) with
| (bv, aq) -> begin
(

let uu____5642 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5642), (aq)))
end)) bs)
in (mk_app f uu____5596)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____5692 = (FStar_Ident.range_of_lid l)
in (

let uu____5693 = (

let uu____5702 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____5702))
in (uu____5693 FStar_Pervasives_Native.None uu____5692)))
end
| uu____5707 -> begin
(

let e = (

let uu____5721 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____5721 args))
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
| uu____5772 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText itext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[]))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____5798 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5798) with
| true -> begin
(

let uu____5801 = (

let uu____5807 = (

let uu____5809 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "_" uu____5809))
in (

let uu____5812 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____5807), (uu____5812))))
in (FStar_Ident.mk_ident uu____5801))
end
| uu____5814 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___941_5817 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___941_5817.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___941_5817.FStar_Syntax_Syntax.sort})
in (

let uu____5818 = (mk_field_projector_name_from_ident lid nm)
in ((uu____5818), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____5830) -> begin
ses
end
| uu____5839 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____5854 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____5854) with
| FStar_Pervasives_Native.Some (uu____5857) -> begin
(

let uu____5858 = (

let uu____5860 = (

let uu____5862 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5862))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5860))
in (failwith uu____5858))
end
| uu____5867 -> begin
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
| uu____5950 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____5996 = (

let uu___998_5997 = rc
in (

let uu____5998 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___998_5997.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5998; FStar_Syntax_Syntax.residual_flags = uu___998_5997.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____5996))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____6015 -> begin
(

let body = (

let uu____6017 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____6017))
in (match (body.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt') -> begin
(

let uu____6047 = (

let uu____6054 = (

let uu____6055 = (

let uu____6074 = (

let uu____6083 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____6083 bs'))
in (

let uu____6098 = (close_lopt lopt')
in ((uu____6074), (t1), (uu____6098))))
in FStar_Syntax_Syntax.Tm_abs (uu____6055))
in (FStar_Syntax_Syntax.mk uu____6054))
in (uu____6047 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____6113 -> begin
(

let uu____6114 = (

let uu____6121 = (

let uu____6122 = (

let uu____6141 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____6150 = (close_lopt lopt)
in ((uu____6141), (body), (uu____6150))))
in FStar_Syntax_Syntax.Tm_abs (uu____6122))
in (FStar_Syntax_Syntax.mk uu____6121))
in (uu____6114 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____6206 -> begin
(

let uu____6215 = (

let uu____6222 = (

let uu____6223 = (

let uu____6238 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____6247 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____6238), (uu____6247))))
in FStar_Syntax_Syntax.Tm_arrow (uu____6223))
in (FStar_Syntax_Syntax.mk uu____6222))
in (uu____6215 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____6296 = (

let uu____6297 = (FStar_Syntax_Subst.compress t)
in uu____6297.FStar_Syntax_Syntax.n)
in (match (uu____6296) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____6327) -> begin
(

let uu____6336 = (

let uu____6337 = (FStar_Syntax_Subst.compress tres)
in uu____6337.FStar_Syntax_Syntax.n)
in (match (uu____6336) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____6380 -> begin
t
end))
end
| uu____6381 -> begin
t
end)
end
| uu____6382 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____6400 = (

let uu____6401 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____6401 t.FStar_Syntax_Syntax.pos))
in (

let uu____6402 = (

let uu____6409 = (

let uu____6410 = (

let uu____6417 = (

let uu____6420 = (

let uu____6421 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____6421)::[])
in (FStar_Syntax_Subst.close uu____6420 t))
in ((b), (uu____6417)))
in FStar_Syntax_Syntax.Tm_refine (uu____6410))
in (FStar_Syntax_Syntax.mk uu____6409))
in (uu____6402 FStar_Pervasives_Native.None uu____6400))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6501 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6501) with
| (bs1, c1) -> begin
(

let uu____6520 = (is_total_comp c1)
in (match (uu____6520) with
| true -> begin
(

let uu____6535 = (arrow_formals_comp (comp_result c1))
in (match (uu____6535) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____6592 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6602; FStar_Syntax_Syntax.index = uu____6603; FStar_Syntax_Syntax.sort = s}, uu____6605) -> begin
(

let rec aux = (fun s1 k2 -> (

let uu____6636 = (

let uu____6637 = (FStar_Syntax_Subst.compress s1)
in uu____6637.FStar_Syntax_Syntax.n)
in (match (uu____6636) with
| FStar_Syntax_Syntax.Tm_arrow (uu____6652) -> begin
(arrow_formals_comp s1)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6667; FStar_Syntax_Syntax.index = uu____6668; FStar_Syntax_Syntax.sort = s2}, uu____6670) -> begin
(aux s2 k2)
end
| uu____6678 -> begin
(

let uu____6679 = (FStar_Syntax_Syntax.mk_Total k2)
in (([]), (uu____6679)))
end)))
in (aux s k1))
end
| uu____6694 -> begin
(

let uu____6695 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____6695)))
end)))


let arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____6730 = (arrow_formals_comp k)
in (match (uu____6730) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let let_rec_arity : FStar_Syntax_Syntax.letbinding  ->  (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option) = (fun lb -> (

let rec arrow_until_decreases = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6872 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6872) with
| (bs1, c1) -> begin
(

let ct = (comp_to_comp_typ c1)
in (

let uu____6896 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.find_opt (fun uu___8_6905 -> (match (uu___8_6905) with
| FStar_Syntax_Syntax.DECREASES (uu____6907) -> begin
true
end
| uu____6911 -> begin
false
end))))
in (match (uu____6896) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (d)) -> begin
((bs1), (FStar_Pervasives_Native.Some (d)))
end
| uu____6946 -> begin
(

let uu____6949 = (is_total_comp c1)
in (match (uu____6949) with
| true -> begin
(

let uu____6968 = (arrow_until_decreases (comp_result c1))
in (match (uu____6968) with
| (bs', d) -> begin
(((FStar_List.append bs1 bs')), (d))
end))
end
| uu____7045 -> begin
((bs1), (FStar_Pervasives_Native.None))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____7061; FStar_Syntax_Syntax.index = uu____7062; FStar_Syntax_Syntax.sort = k2}, uu____7064) -> begin
(arrow_until_decreases k2)
end
| uu____7072 -> begin
(([]), (FStar_Pervasives_Native.None))
end)))
in (

let uu____7093 = (arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____7093) with
| (bs, dopt) -> begin
(

let n_univs = (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
in (

let uu____7147 = (FStar_Util.map_opt dopt (fun d -> (

let d_bvs = (FStar_Syntax_Free.names d)
in (

let uu____7168 = (FStar_Common.tabulate n_univs (fun uu____7174 -> false))
in (

let uu____7177 = (FStar_All.pipe_right bs (FStar_List.map (fun uu____7202 -> (match (uu____7202) with
| (x, uu____7211) -> begin
(FStar_Util.set_mem x d_bvs)
end))))
in (FStar_List.append uu____7168 uu____7177))))))
in (((n_univs + (FStar_List.length bs))), (uu____7147))))
end))))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____7267 = (

let uu___1120_7268 = rc
in (

let uu____7269 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___1120_7268.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____7269; FStar_Syntax_Syntax.residual_flags = uu___1120_7268.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____7267))
end
| uu____7278 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____7312 = (

let uu____7313 = (

let uu____7316 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____7316))
in uu____7313.FStar_Syntax_Syntax.n)
in (match (uu____7312) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____7362 = (aux t2 what)
in (match (uu____7362) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____7434 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____7451 = (aux t FStar_Pervasives_Native.None)
in (match (uu____7451) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____7499 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____7499) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____7662) -> begin
def
end
| (uu____7673, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____7685) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _7701 -> FStar_Syntax_Syntax.U_name (_7701))))
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

let uu____7783 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____7783) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____7818 -> begin
(

let t' = (arrow binders c)
in (

let uu____7830 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____7830) with
| (uvs1, t'1) -> begin
(

let uu____7851 = (

let uu____7852 = (FStar_Syntax_Subst.compress t'1)
in uu____7852.FStar_Syntax_Syntax.n)
in (match (uu____7851) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____7901 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____7926 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____7937 -> begin
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

let uu____8000 = (

let uu____8001 = (pre_typ t)
in uu____8001.FStar_Syntax_Syntax.n)
in (match (uu____8000) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____8006 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____8020 = (

let uu____8021 = (pre_typ t)
in uu____8021.FStar_Syntax_Syntax.n)
in (match (uu____8020) with
| FStar_Syntax_Syntax.Tm_fvar (uu____8025) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____8027) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____8053) -> begin
(is_constructed_typ t1 lid)
end
| uu____8058 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____8071) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____8072) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____8073) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____8075) -> begin
(get_tycon t2)
end
| uu____8100 -> begin
FStar_Pervasives_Native.None
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____8108 = (

let uu____8109 = (un_uinst t)
in uu____8109.FStar_Syntax_Syntax.n)
in (match (uu____8108) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____8114 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____8128 = (

let uu____8132 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____8132))
in (match (uu____8128) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____8164 -> begin
false
end))
end
| uu____8169 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____8183 -> (

let u = (

let uu____8189 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _8206 -> FStar_Syntax_Syntax.U_unif (_8206)) uu____8189))
in (

let uu____8207 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____8207), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____8220 = (eq_tm a a')
in (match (uu____8220) with
| Equal -> begin
true
end
| uu____8223 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____8228 = (

let uu____8235 = (

let uu____8236 = (

let uu____8237 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____8237 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____8236))
in (FStar_Syntax_Syntax.mk uu____8235))
in (uu____8228 FStar_Pervasives_Native.None FStar_Range.dummyRange))


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

let uu____8349 = (

let uu____8352 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____8353 = (

let uu____8360 = (

let uu____8361 = (

let uu____8378 = (

let uu____8389 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____8398 = (

let uu____8409 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____8409)::[])
in (uu____8389)::uu____8398))
in ((tand), (uu____8378)))
in FStar_Syntax_Syntax.Tm_app (uu____8361))
in (FStar_Syntax_Syntax.mk uu____8360))
in (uu____8353 FStar_Pervasives_Native.None uu____8352)))
in FStar_Pervasives_Native.Some (uu____8349))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____8486 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____8487 = (

let uu____8494 = (

let uu____8495 = (

let uu____8512 = (

let uu____8523 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____8532 = (

let uu____8543 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____8543)::[])
in (uu____8523)::uu____8532))
in ((op_t), (uu____8512)))
in FStar_Syntax_Syntax.Tm_app (uu____8495))
in (FStar_Syntax_Syntax.mk uu____8494))
in (uu____8487 FStar_Pervasives_Native.None uu____8486))))


let mk_neg : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____8600 = (

let uu____8607 = (

let uu____8608 = (

let uu____8625 = (

let uu____8636 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____8636)::[])
in ((t_not), (uu____8625)))
in FStar_Syntax_Syntax.Tm_app (uu____8608))
in (FStar_Syntax_Syntax.mk uu____8607))
in (uu____8600 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


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

let uu____8833 = (

let uu____8840 = (

let uu____8841 = (

let uu____8858 = (

let uu____8869 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8869)::[])
in ((b2t_v), (uu____8858)))
in FStar_Syntax_Syntax.Tm_app (uu____8841))
in (FStar_Syntax_Syntax.mk uu____8840))
in (uu____8833 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let unb2t : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e -> (

let uu____8916 = (head_and_args e)
in (match (uu____8916) with
| (hd1, args) -> begin
(

let uu____8961 = (

let uu____8976 = (

let uu____8977 = (FStar_Syntax_Subst.compress hd1)
in uu____8977.FStar_Syntax_Syntax.n)
in ((uu____8976), (args)))
in (match (uu____8961) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e1, uu____8994))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid) -> begin
FStar_Pervasives_Native.Some (e1)
end
| uu____9029 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_t_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9051 = (

let uu____9052 = (unmeta t)
in uu____9052.FStar_Syntax_Syntax.n)
in (match (uu____9051) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____9057 -> begin
false
end)))


let mk_conj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____9080 = (is_t_true t1)
in (match (uu____9080) with
| true -> begin
t2
end
| uu____9085 -> begin
(

let uu____9087 = (is_t_true t2)
in (match (uu____9087) with
| true -> begin
t1
end
| uu____9092 -> begin
(mk_conj t1 t2)
end))
end)))


let mk_disj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____9115 = (is_t_true t1)
in (match (uu____9115) with
| true -> begin
t_true
end
| uu____9120 -> begin
(

let uu____9122 = (is_t_true t2)
in (match (uu____9122) with
| true -> begin
t_true
end
| uu____9127 -> begin
(mk_disj t1 t2)
end))
end)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____9151 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____9152 = (

let uu____9159 = (

let uu____9160 = (

let uu____9177 = (

let uu____9188 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____9197 = (

let uu____9208 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____9208)::[])
in (uu____9188)::uu____9197))
in ((teq), (uu____9177)))
in FStar_Syntax_Syntax.Tm_app (uu____9160))
in (FStar_Syntax_Syntax.mk uu____9159))
in (uu____9152 FStar_Pervasives_Native.None uu____9151))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____9275 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____9276 = (

let uu____9283 = (

let uu____9284 = (

let uu____9301 = (

let uu____9312 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9321 = (

let uu____9332 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____9341 = (

let uu____9352 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____9352)::[])
in (uu____9332)::uu____9341))
in (uu____9312)::uu____9321))
in ((eq_inst), (uu____9301)))
in FStar_Syntax_Syntax.Tm_app (uu____9284))
in (FStar_Syntax_Syntax.mk uu____9283))
in (uu____9276 FStar_Pervasives_Native.None uu____9275)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____9429 = (

let uu____9436 = (

let uu____9437 = (

let uu____9454 = (

let uu____9465 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9474 = (

let uu____9485 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____9494 = (

let uu____9505 = (FStar_Syntax_Syntax.as_arg t')
in (uu____9505)::[])
in (uu____9485)::uu____9494))
in (uu____9465)::uu____9474))
in ((t_has_type1), (uu____9454)))
in FStar_Syntax_Syntax.Tm_app (uu____9437))
in (FStar_Syntax_Syntax.mk uu____9436))
in (uu____9429 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____9582 = (

let uu____9589 = (

let uu____9590 = (

let uu____9607 = (

let uu____9618 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____9627 = (

let uu____9638 = (FStar_Syntax_Syntax.as_arg e)
in (uu____9638)::[])
in (uu____9618)::uu____9627))
in ((t_with_type1), (uu____9607)))
in FStar_Syntax_Syntax.Tm_app (uu____9590))
in (FStar_Syntax_Syntax.mk uu____9589))
in (uu____9582 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (

let uu____9685 = (

let uu____9692 = (

let uu____9693 = (

let uu____9700 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____9700), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____9693))
in (FStar_Syntax_Syntax.mk uu____9692))
in (uu____9685 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflag Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____9783 = (

let uu____9790 = (

let uu____9791 = (

let uu____9808 = (

let uu____9819 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____9828 = (

let uu____9839 = (

let uu____9848 = (

let uu____9849 = (

let uu____9850 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9850)::[])
in (abs uu____9849 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____9848))
in (uu____9839)::[])
in (uu____9819)::uu____9828))
in ((fa), (uu____9808)))
in FStar_Syntax_Syntax.Tm_app (uu____9791))
in (FStar_Syntax_Syntax.mk uu____9790))
in (uu____9783 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____9977 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____9977) with
| true -> begin
f1
end
| uu____9980 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____9996) -> begin
true
end
| uu____9998 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____10045 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____10045), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____10074 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____10074), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____10088 = (

let uu____10089 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10089))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____10088)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10165 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____10168 = (

let uu____10179 = (FStar_Syntax_Syntax.as_arg p)
in (uu____10179)::[])
in (mk_app uu____10165 uu____10168)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____10219 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____10222 = (

let uu____10233 = (FStar_Syntax_Syntax.as_arg p)
in (uu____10233)::[])
in (mk_app uu____10219 uu____10222)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____10268 = (head_and_args t)
in (match (uu____10268) with
| (head1, args) -> begin
(

let head2 = (unascribe head1)
in (

let head3 = (un_uinst head2)
in (

let uu____10317 = (

let uu____10332 = (

let uu____10333 = (FStar_Syntax_Subst.compress head3)
in uu____10333.FStar_Syntax_Syntax.n)
in ((uu____10332), (args)))
in (match (uu____10317) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____10352))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____10418 = (

let uu____10423 = (

let uu____10424 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____10424)::[])
in (FStar_Syntax_Subst.open_term uu____10423 p))
in (match (uu____10418) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____10481 -> begin
(failwith "impossible")
end)
in (

let uu____10489 = (

let uu____10491 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____10491))
in (match (uu____10489) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____10503 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____10507 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10510 -> begin
FStar_Pervasives_Native.None
end))))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____10541 = (head_and_args t)
in (match (uu____10541) with
| (head1, args) -> begin
(

let uu____10592 = (

let uu____10607 = (

let uu____10608 = (FStar_Syntax_Subst.compress head1)
in uu____10608.FStar_Syntax_Syntax.n)
in ((uu____10607), (args)))
in (match (uu____10592) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10630; FStar_Syntax_Syntax.vars = uu____10631}, (u)::[]), ((t1, uu____10634))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____10681 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____10716 = (head_and_args t)
in (match (uu____10716) with
| (head1, args) -> begin
(

let uu____10767 = (

let uu____10782 = (

let uu____10783 = (FStar_Syntax_Subst.compress head1)
in uu____10783.FStar_Syntax_Syntax.n)
in ((uu____10782), (args)))
in (match (uu____10767) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10805; FStar_Syntax_Syntax.vars = uu____10806}, (u)::[]), ((t1, uu____10809))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____10856 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____10884 = (

let uu____10901 = (unmeta t)
in (head_and_args uu____10901))
in (match (uu____10884) with
| (head1, uu____10904) -> begin
(

let uu____10929 = (

let uu____10930 = (un_uinst head1)
in uu____10930.FStar_Syntax_Syntax.n)
in (match (uu____10929) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____10935 -> begin
false
end))
end)))


let arrow_one_ln : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____10955 = (

let uu____10956 = (FStar_Syntax_Subst.compress t)
in uu____10956.FStar_Syntax_Syntax.n)
in (match (uu____10955) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____11062 = (

let uu____11067 = (

let uu____11068 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____11068))
in ((b), (uu____11067)))
in FStar_Pervasives_Native.Some (uu____11062))
end
| uu____11073 -> begin
FStar_Pervasives_Native.None
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____11096 = (arrow_one_ln t)
in (FStar_Util.bind_opt uu____11096 (fun uu____11124 -> (match (uu____11124) with
| (b, c) -> begin
(

let uu____11143 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____11143) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____11206 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____11243 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____11243)))


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
| uu____11295 -> begin
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
| uu____11338 -> begin
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
| uu____11379 -> begin
false
end))


let __proj__BaseConn__item___0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
_0
end))


let destruct_base_table : (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list) Prims.list = (

let f = (fun x -> ((x), (x)))
in ((((Prims.parse_int "0")), (((f FStar_Parser_Const.true_lid))::((f FStar_Parser_Const.false_lid))::[])))::((((Prims.parse_int "2")), (((f FStar_Parser_Const.and_lid))::((f FStar_Parser_Const.or_lid))::((f FStar_Parser_Const.imp_lid))::((f FStar_Parser_Const.iff_lid))::((f FStar_Parser_Const.eq2_lid))::((f FStar_Parser_Const.eq3_lid))::[])))::((((Prims.parse_int "1")), (((f FStar_Parser_Const.not_lid))::[])))::((((Prims.parse_int "3")), (((f FStar_Parser_Const.ite_lid))::((f FStar_Parser_Const.eq2_lid))::[])))::((((Prims.parse_int "4")), (((f FStar_Parser_Const.eq3_lid))::[])))::[])


let destruct_sq_base_table : (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list) Prims.list = ((((Prims.parse_int "2")), ((((FStar_Parser_Const.c_and_lid), (FStar_Parser_Const.and_lid)))::(((FStar_Parser_Const.c_or_lid), (FStar_Parser_Const.or_lid)))::(((FStar_Parser_Const.c_eq2_lid), (FStar_Parser_Const.c_eq2_lid)))::(((FStar_Parser_Const.c_eq3_lid), (FStar_Parser_Const.c_eq3_lid)))::[])))::((((Prims.parse_int "3")), ((((FStar_Parser_Const.c_eq2_lid), (FStar_Parser_Const.c_eq2_lid)))::[])))::((((Prims.parse_int "4")), ((((FStar_Parser_Const.c_eq3_lid), (FStar_Parser_Const.c_eq3_lid)))::[])))::((((Prims.parse_int "0")), ((((FStar_Parser_Const.c_true_lid), (FStar_Parser_Const.true_lid)))::(((FStar_Parser_Const.c_false_lid), (FStar_Parser_Const.false_lid)))::[])))::[]


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective FStar_Pervasives_Native.option = (fun f -> (

let rec unmeta_monadic = (fun f1 -> (

let f2 = (FStar_Syntax_Subst.compress f1)
in (match (f2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____11765)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____11777)) -> begin
(unmeta_monadic t)
end
| uu____11790 -> begin
f2
end)))
in (

let lookup_arity_lid = (fun table target_lid args -> (

let arg_len = (FStar_List.length args)
in (

let aux = (fun uu____11859 -> (match (uu____11859) with
| (arity, lids) -> begin
(match ((Prims.op_Equality arg_len arity)) with
| true -> begin
(FStar_Util.find_map lids (fun uu____11897 -> (match (uu____11897) with
| (lid, out_lid) -> begin
(

let uu____11906 = (FStar_Ident.lid_equals target_lid lid)
in (match (uu____11906) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((out_lid), (args))))
end
| uu____11911 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____11913 -> begin
FStar_Pervasives_Native.None
end)
end))
in (FStar_Util.find_map table aux))))
in (

let destruct_base_conn = (fun t -> (

let uu____11933 = (head_and_args t)
in (match (uu____11933) with
| (hd1, args) -> begin
(

let uu____11978 = (

let uu____11979 = (un_uinst hd1)
in uu____11979.FStar_Syntax_Syntax.n)
in (match (uu____11978) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(lookup_arity_lid destruct_base_table fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v args)
end
| uu____11985 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (

let destruct_sq_base_conn = (fun t -> (

let uu____11994 = (un_squash t)
in (FStar_Util.bind_opt uu____11994 (fun t1 -> (

let uu____12010 = (head_and_args' t1)
in (match (uu____12010) with
| (hd1, args) -> begin
(

let uu____12049 = (

let uu____12050 = (un_uinst hd1)
in uu____12050.FStar_Syntax_Syntax.n)
in (match (uu____12049) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(lookup_arity_lid destruct_sq_base_table fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v args)
end
| uu____12056 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let patterns = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (uu____12097, pats)) -> begin
(

let uu____12135 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____12135)))
end
| uu____12148 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____12195 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____12215 = (head_and_args t1)
in (match (uu____12215) with
| (t2, args) -> begin
(

let uu____12270 = (un_uinst t2)
in (

let uu____12271 = (FStar_All.pipe_right args (FStar_List.map (fun uu____12312 -> (match (uu____12312) with
| (t3, imp) -> begin
(

let uu____12331 = (unascribe t3)
in ((uu____12331), (imp)))
end))))
in ((uu____12270), (uu____12271))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____12382 = (

let uu____12406 = (flat t1)
in ((qopt), (uu____12406)))
in (match (uu____12382) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12446; FStar_Syntax_Syntax.vars = uu____12447}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12450); FStar_Syntax_Syntax.pos = uu____12451; FStar_Syntax_Syntax.vars = uu____12452}, uu____12453))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12555; FStar_Syntax_Syntax.vars = uu____12556}, (uu____12557)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12560); FStar_Syntax_Syntax.pos = uu____12561; FStar_Syntax_Syntax.vars = uu____12562}, uu____12563))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12680; FStar_Syntax_Syntax.vars = uu____12681}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12684); FStar_Syntax_Syntax.pos = uu____12685; FStar_Syntax_Syntax.vars = uu____12686}, uu____12687))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____12780 = (

let uu____12784 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____12784))
in (aux uu____12780 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____12794; FStar_Syntax_Syntax.vars = uu____12795}, (uu____12796)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____12799); FStar_Syntax_Syntax.pos = uu____12800; FStar_Syntax_Syntax.vars = uu____12801}, uu____12802))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____12911 = (

let uu____12915 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____12915))
in (aux uu____12911 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____12925) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____12978 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____12978) with
| (bs1, t2) -> begin
(

let uu____12987 = (patterns t2)
in (match (uu____12987) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____13035 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____13037 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____13092 = (un_squash t)
in (FStar_Util.bind_opt uu____13092 (fun t1 -> (

let uu____13107 = (arrow_one t1)
in (match (uu____13107) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____13122 = (

let uu____13124 = (is_tot_or_gtot_comp c)
in (not (uu____13124)))
in (match (uu____13122) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13129 -> begin
(

let q = (

let uu____13134 = (comp_to_comp_typ_nouniv c)
in uu____13134.FStar_Syntax_Syntax.result_typ)
in (

let uu____13135 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____13135) with
| true -> begin
(

let uu____13142 = (patterns q)
in (match (uu____13142) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____13203 -> begin
(

let uu____13205 = (

let uu____13206 = (

let uu____13211 = (

let uu____13212 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____13223 = (

let uu____13234 = (FStar_Syntax_Syntax.as_arg q)
in (uu____13234)::[])
in (uu____13212)::uu____13223))
in ((FStar_Parser_Const.imp_lid), (uu____13211)))
in BaseConn (uu____13206))
in FStar_Pervasives_Native.Some (uu____13205))
end)))
end))
end
| uu____13267 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____13275 = (un_squash t)
in (FStar_Util.bind_opt uu____13275 (fun t1 -> (

let uu____13306 = (head_and_args' t1)
in (match (uu____13306) with
| (hd1, args) -> begin
(

let uu____13345 = (

let uu____13360 = (

let uu____13361 = (un_uinst hd1)
in uu____13361.FStar_Syntax_Syntax.n)
in ((uu____13360), (args)))
in (match (uu____13345) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____13378))::((a2, uu____13380))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____13431 = (

let uu____13432 = (FStar_Syntax_Subst.compress a2)
in uu____13432.FStar_Syntax_Syntax.n)
in (match (uu____13431) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____13439) -> begin
(

let uu____13474 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____13474) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____13527 -> begin
(failwith "impossible")
end)
in (

let uu____13535 = (patterns q1)
in (match (uu____13535) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____13596 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____13597 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____13620 = (destruct_sq_forall phi)
in (match (uu____13620) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _13630 -> FStar_Pervasives_Native.Some (_13630)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____13637 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____13643 = (destruct_sq_exists phi)
in (match (uu____13643) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _13653 -> FStar_Pervasives_Native.Some (_13653)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____13660 -> begin
f1
end))
end
| uu____13663 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____13667 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____13667 (fun uu____13672 -> (

let uu____13673 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____13673 (fun uu____13678 -> (

let uu____13679 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____13679 (fun uu____13684 -> (

let uu____13685 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____13685 (fun uu____13690 -> (

let uu____13691 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____13691 (fun uu____13695 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____13713 = (

let uu____13718 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____13718))
in (

let uu____13719 = (

let uu____13720 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____13720))
in (

let uu____13723 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____13713 a.FStar_Syntax_Syntax.action_univs uu____13719 FStar_Parser_Const.effect_Tot_lid uu____13723 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____13749 = (

let uu____13756 = (

let uu____13757 = (

let uu____13774 = (

let uu____13785 = (FStar_Syntax_Syntax.as_arg t)
in (uu____13785)::[])
in ((reify_1), (uu____13774)))
in FStar_Syntax_Syntax.Tm_app (uu____13757))
in (FStar_Syntax_Syntax.mk uu____13756))
in (uu____13749 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let mk_reflect : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reflect_ = (

let uu____13837 = (

let uu____13844 = (

let uu____13845 = (

let uu____13846 = (FStar_Ident.lid_of_str "Bogus.Effect")
in FStar_Const.Const_reflect (uu____13846))
in FStar_Syntax_Syntax.Tm_constant (uu____13845))
in (FStar_Syntax_Syntax.mk uu____13844))
in (uu____13837 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____13848 = (

let uu____13855 = (

let uu____13856 = (

let uu____13873 = (

let uu____13884 = (FStar_Syntax_Syntax.as_arg t)
in (uu____13884)::[])
in ((reflect_), (uu____13873)))
in FStar_Syntax_Syntax.Tm_app (uu____13856))
in (FStar_Syntax_Syntax.mk uu____13855))
in (uu____13848 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____13928) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____13953 = (unfold_lazy i)
in (delta_qualifier uu____13953))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____13955) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____13956) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____13957) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____13980) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____13993) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____13994) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____14001) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____14002) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____14018) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____14023; FStar_Syntax_Syntax.index = uu____14024; FStar_Syntax_Syntax.sort = t2}, uu____14026) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____14035) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____14041, uu____14042) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____14084) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____14109, t2, uu____14111) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____14136, t2) -> begin
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

let uu____14175 = (delta_qualifier t)
in (incr_delta_depth uu____14175)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____14183 = (

let uu____14184 = (FStar_Syntax_Subst.compress t)
in uu____14184.FStar_Syntax_Syntax.n)
in (match (uu____14183) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____14189 -> begin
false
end)))


let rec apply_last : 'Auu____14198 . ('Auu____14198  ->  'Auu____14198)  ->  'Auu____14198 Prims.list  ->  'Auu____14198 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____14224 = (f a)
in (uu____14224)::[])
end
| (x)::xs -> begin
(

let uu____14229 = (apply_last f xs)
in (x)::uu____14229)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____14284 = (

let uu____14291 = (

let uu____14292 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____14292))
in (FStar_Syntax_Syntax.mk uu____14291))
in (uu____14284 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____14306 = (

let uu____14311 = (

let uu____14312 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____14312 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____14311 args))
in (uu____14306 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____14326 = (

let uu____14331 = (

let uu____14332 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____14332 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____14331 args))
in (uu____14326 FStar_Pervasives_Native.None pos)))
in (

let uu____14333 = (

let uu____14334 = (

let uu____14335 = (FStar_Syntax_Syntax.iarg typ)
in (uu____14335)::[])
in (nil uu____14334 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____14369 = (

let uu____14370 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____14379 = (

let uu____14390 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____14399 = (

let uu____14410 = (FStar_Syntax_Syntax.as_arg a)
in (uu____14410)::[])
in (uu____14390)::uu____14399))
in (uu____14370)::uu____14379))
in (cons1 uu____14369 t.FStar_Syntax_Syntax.pos))) l uu____14333))))))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____14519 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____14633 -> begin
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
| uu____14799 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____14834 -> begin
((

let uu____14837 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____14837) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____14862 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____15041 = (unmeta_safe t1)
in (canon_app uu____15041))
in (

let t21 = (

let uu____15047 = (unmeta_safe t2)
in (canon_app uu____15047))
in (

let uu____15050 = (

let uu____15055 = (

let uu____15056 = (

let uu____15059 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____15059))
in uu____15056.FStar_Syntax_Syntax.n)
in (

let uu____15060 = (

let uu____15061 = (

let uu____15064 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____15064))
in uu____15061.FStar_Syntax_Syntax.n)
in ((uu____15055), (uu____15060))))
in (match (uu____15050) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____15066), uu____15067) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15076, FStar_Syntax_Syntax.Tm_uinst (uu____15077)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____15086), uu____15087) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15112, FStar_Syntax_Syntax.Tm_delayed (uu____15113)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____15138), uu____15139) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____15168, FStar_Syntax_Syntax.Tm_ascribed (uu____15169)) -> begin
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

let uu____15208 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____15208))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____15213 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____15213))
end
| (FStar_Syntax_Syntax.Tm_type (uu____15216), FStar_Syntax_Syntax.Tm_type (uu____15217)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____15275 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____15275)) && (

let uu____15285 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____15285)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____15334 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____15334)) && (

let uu____15344 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____15344)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((

let uu____15361 = (term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort b2.FStar_Syntax_Syntax.sort)
in (check "refine bv sort" uu____15361)) && (

let uu____15365 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____15365)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____15422 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____15422)) && (

let uu____15426 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____15426)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____15515 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____15515)) && (

let uu____15519 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____15519)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____15536), uu____15537) -> begin
(

let uu____15538 = (

let uu____15540 = (unlazy t11)
in (term_eq_dbg dbg uu____15540 t21))
in (check "lazy_l" uu____15538))
end
| (uu____15542, FStar_Syntax_Syntax.Tm_lazy (uu____15543)) -> begin
(

let uu____15544 = (

let uu____15546 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____15546))
in (check "lazy_r" uu____15544))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____15591 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____15591))) && (

let uu____15595 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____15595)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____15599), FStar_Syntax_Syntax.Tm_uvar (u2, uu____15601)) -> begin
(check "uvar" (Prims.op_Equality u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((

let uu____15659 = (

let uu____15661 = (eq_quoteinfo qi1 qi2)
in (Prims.op_Equality uu____15661 Equal))
in (check "tm_quoted qi" uu____15659)) && (

let uu____15664 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____15664)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____15694 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____15694)) && (

let uu____15698 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____15698)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____15717 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____15717)) && (

let uu____15721 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____15721))) && (

let uu____15725 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____15725)))
end
| uu____15728 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____15734) -> begin
(fail "unk")
end
| (uu____15736, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____15738), uu____15739) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____15741), uu____15742) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____15744), uu____15745) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____15747), uu____15748) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____15750), uu____15751) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____15753), uu____15754) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____15774), uu____15775) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____15791), uu____15792) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____15800), uu____15801) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____15819), uu____15820) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____15844), uu____15845) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____15860), uu____15861) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____15875), uu____15876) -> begin
(fail "bottom")
end
| (uu____15884, FStar_Syntax_Syntax.Tm_bvar (uu____15885)) -> begin
(fail "bottom")
end
| (uu____15887, FStar_Syntax_Syntax.Tm_name (uu____15888)) -> begin
(fail "bottom")
end
| (uu____15890, FStar_Syntax_Syntax.Tm_fvar (uu____15891)) -> begin
(fail "bottom")
end
| (uu____15893, FStar_Syntax_Syntax.Tm_constant (uu____15894)) -> begin
(fail "bottom")
end
| (uu____15896, FStar_Syntax_Syntax.Tm_type (uu____15897)) -> begin
(fail "bottom")
end
| (uu____15899, FStar_Syntax_Syntax.Tm_abs (uu____15900)) -> begin
(fail "bottom")
end
| (uu____15920, FStar_Syntax_Syntax.Tm_arrow (uu____15921)) -> begin
(fail "bottom")
end
| (uu____15937, FStar_Syntax_Syntax.Tm_refine (uu____15938)) -> begin
(fail "bottom")
end
| (uu____15946, FStar_Syntax_Syntax.Tm_app (uu____15947)) -> begin
(fail "bottom")
end
| (uu____15965, FStar_Syntax_Syntax.Tm_match (uu____15966)) -> begin
(fail "bottom")
end
| (uu____15990, FStar_Syntax_Syntax.Tm_let (uu____15991)) -> begin
(fail "bottom")
end
| (uu____16006, FStar_Syntax_Syntax.Tm_uvar (uu____16007)) -> begin
(fail "bottom")
end
| (uu____16021, FStar_Syntax_Syntax.Tm_meta (uu____16022)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____16057 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____16057))) (fun q1 q2 -> (

let uu____16069 = (

let uu____16071 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____16071 Equal))
in (check "arg qual" uu____16069))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____16096 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____16096))) (fun q1 q2 -> (

let uu____16108 = (

let uu____16110 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____16110 Equal))
in (check "binder qual" uu____16108))) b1 b2))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____16124 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____16124)) && (

let uu____16128 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____16128))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflag  ->  FStar_Syntax_Syntax.cflag  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____16138 uu____16139 -> (match (((uu____16138), (uu____16139))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____16266 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____16266)) && (

let uu____16270 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____16270))) && (

let uu____16274 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____16316 -> begin
false
end)
in (check "branch when" uu____16274)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____16337 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____16337)) && (

let uu____16346 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____16346))) && (

let uu____16350 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____16350))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____16367 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____16367 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____16421) -> begin
(

let uu____16444 = (

let uu____16446 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____16446))
in ((Prims.parse_int "1") + uu____16444))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____16449 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____16449))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____16453 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____16453))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____16462 = (sizeof t1)
in ((FStar_List.length us) + uu____16462))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____16466) -> begin
(

let uu____16491 = (sizeof t1)
in (

let uu____16493 = (FStar_List.fold_left (fun acc uu____16508 -> (match (uu____16508) with
| (bv, uu____16518) -> begin
(

let uu____16523 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____16523))
end)) (Prims.parse_int "0") bs)
in (uu____16491 + uu____16493)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____16552 = (sizeof hd1)
in (

let uu____16554 = (FStar_List.fold_left (fun acc uu____16569 -> (match (uu____16569) with
| (arg, uu____16579) -> begin
(

let uu____16584 = (sizeof arg)
in (acc + uu____16584))
end)) (Prims.parse_int "0") args)
in (uu____16552 + uu____16554)))
end
| uu____16587 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____16601 = (

let uu____16602 = (un_uinst t)
in uu____16602.FStar_Syntax_Syntax.n)
in (match (uu____16601) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____16607 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let get_attribute : FStar_Ident.lident  ->  FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Syntax_Syntax.args FStar_Pervasives_Native.option = (fun attr attrs -> (FStar_List.tryPick (fun t -> (

let uu____16668 = (head_and_args t)
in (match (uu____16668) with
| (head1, args) -> begin
(

let uu____16723 = (

let uu____16724 = (FStar_Syntax_Subst.compress head1)
in uu____16724.FStar_Syntax_Syntax.n)
in (match (uu____16723) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv attr) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____16750 -> begin
FStar_Pervasives_Native.None
end))
end))) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun s -> (

let uu____16780 = (FStar_Options.set_options s)
in (match (uu____16780) with
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
(FStar_Options.set_ml_ish ())
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____16794 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____16794 (fun a1 -> ())));
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 s)
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
(set_options1 s)
end);
)
end
| FStar_Syntax_Syntax.RestartSolver -> begin
()
end
| FStar_Syntax_Syntax.PopOptions -> begin
(

let uu____16809 = (FStar_Options.internal_pop ())
in (match (uu____16809) with
| true -> begin
()
end
| uu____16812 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ("Cannot #pop-options, stack would become empty")) r)
end))
end)))


let rec unbound_variables : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun tm -> (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____16841) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____16868) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____16883) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____16884) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____16885) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____16894) -> begin
(

let uu____16919 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____16919) with
| (bs1, t2) -> begin
(

let uu____16928 = (FStar_List.collect (fun uu____16940 -> (match (uu____16940) with
| (b, uu____16950) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____16955 = (unbound_variables t2)
in (FStar_List.append uu____16928 uu____16955)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____16980 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____16980) with
| (bs1, c1) -> begin
(

let uu____16989 = (FStar_List.collect (fun uu____17001 -> (match (uu____17001) with
| (b, uu____17011) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____17016 = (unbound_variables_comp c1)
in (FStar_List.append uu____16989 uu____17016)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____17025 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____17025) with
| (bs, t2) -> begin
(

let uu____17048 = (FStar_List.collect (fun uu____17060 -> (match (uu____17060) with
| (b1, uu____17070) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____17075 = (unbound_variables t2)
in (FStar_List.append uu____17048 uu____17075)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____17104 = (FStar_List.collect (fun uu____17118 -> (match (uu____17118) with
| (x, uu____17130) -> begin
(unbound_variables x)
end)) args)
in (

let uu____17139 = (unbound_variables t1)
in (FStar_List.append uu____17104 uu____17139)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____17180 = (unbound_variables t1)
in (

let uu____17183 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____17198 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____17198) with
| (p, wopt, t2) -> begin
(

let uu____17220 = (unbound_variables t2)
in (

let uu____17223 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____17220 uu____17223)))
end)))))
in (FStar_List.append uu____17180 uu____17183)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____17237) -> begin
(

let uu____17278 = (unbound_variables t1)
in (

let uu____17281 = (

let uu____17284 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____17315 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____17284 uu____17315)))
in (FStar_List.append uu____17278 uu____17281)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____17356 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____17359 = (

let uu____17362 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____17365 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____17370) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____17372 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____17372) with
| (uu____17393, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____17362 uu____17365)))
in (FStar_List.append uu____17356 uu____17359)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____17395, lbs), t1) -> begin
(

let uu____17415 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____17415) with
| (lbs1, t2) -> begin
(

let uu____17430 = (unbound_variables t2)
in (

let uu____17433 = (FStar_List.collect (fun lb -> (

let uu____17440 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____17443 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____17440 uu____17443)))) lbs1)
in (FStar_List.append uu____17430 uu____17433)))
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

let uu____17460 = (unbound_variables t1)
in (

let uu____17463 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____17468, args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____17523 -> (match (uu____17523) with
| (a, uu____17535) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____17544, uu____17545, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____17551, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____17557) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____17566) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____17567) -> begin
[]
end)
in (FStar_List.append uu____17460 uu____17463)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____17574) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____17584) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____17594 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____17597 = (FStar_List.collect (fun uu____17611 -> (match (uu____17611) with
| (a, uu____17623) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____17594 uu____17597)))
end))


let extract_attr' : FStar_Ident.lid  ->  FStar_Syntax_Syntax.term Prims.list  ->  (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args) FStar_Pervasives_Native.option = (fun attr_lid attrs -> (

let rec aux = (fun acc attrs1 -> (match (attrs1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (h)::t -> begin
(

let uu____17738 = (head_and_args h)
in (match (uu____17738) with
| (head1, args) -> begin
(

let uu____17799 = (

let uu____17800 = (FStar_Syntax_Subst.compress head1)
in uu____17800.FStar_Syntax_Syntax.n)
in (match (uu____17799) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv attr_lid) -> begin
(

let attrs' = (FStar_List.rev_acc acc t)
in FStar_Pervasives_Native.Some (((attrs'), (args))))
end
| uu____17853 -> begin
(aux ((h)::acc) t)
end))
end))
end))
in (aux [] attrs)))


let extract_attr : FStar_Ident.lid  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args) FStar_Pervasives_Native.option = (fun attr_lid se -> (

let uu____17877 = (extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____17877) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (attrs', t) -> begin
FStar_Pervasives_Native.Some ((((

let uu___2457_17919 = se
in {FStar_Syntax_Syntax.sigel = uu___2457_17919.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___2457_17919.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___2457_17919.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___2457_17919.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs'; FStar_Syntax_Syntax.sigopts = uu___2457_17919.FStar_Syntax_Syntax.sigopts})), (t)))
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____17927 = (

let uu____17928 = (FStar_Syntax_Subst.compress t)
in uu____17928.FStar_Syntax_Syntax.n)
in (match (uu____17927) with
| FStar_Syntax_Syntax.Tm_arrow (uu____17932, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____17960))::uu____17961 -> begin
(

let pats' = (unmeta pats)
in (

let uu____18021 = (head_and_args pats')
in (match (uu____18021) with
| (head1, uu____18040) -> begin
(

let uu____18065 = (

let uu____18066 = (un_uinst head1)
in uu____18066.FStar_Syntax_Syntax.n)
in (match (uu____18065) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____18071 -> begin
false
end))
end)))
end
| uu____18073 -> begin
false
end)
end
| uu____18085 -> begin
false
end)
end
| uu____18087 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____18103 = (

let uu____18120 = (unmeta e)
in (head_and_args uu____18120))
in (match (uu____18103) with
| (head1, args) -> begin
(

let uu____18151 = (

let uu____18166 = (

let uu____18167 = (un_uinst head1)
in uu____18167.FStar_Syntax_Syntax.n)
in ((uu____18166), (args)))
in (match (uu____18151) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____18185) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____18209)::((hd1, uu____18211))::((tl1, uu____18213))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____18280 = (

let uu____18283 = (

let uu____18286 = (list_elements tl1)
in (FStar_Util.must uu____18286))
in (hd1)::uu____18283)
in FStar_Pervasives_Native.Some (uu____18280))
end
| uu____18295 -> begin
FStar_Pervasives_Native.None
end))
end)))


let unthunk_lemma_post : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____18324 = (

let uu____18325 = (FStar_Syntax_Subst.compress t)
in uu____18325.FStar_Syntax_Syntax.n)
in (match (uu____18324) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____18332) -> begin
(

let uu____18367 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____18367) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____18401 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____18401) with
| true -> begin
(

let uu____18408 = (

let uu____18419 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____18419)::[])
in (mk_app t uu____18408))
end
| uu____18444 -> begin
e1
end)))
end))
end
| uu____18446 -> begin
(

let uu____18447 = (

let uu____18458 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____18458)::[])
in (mk_app t uu____18447))
end)))


let smt_lemma_as_forall : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universe Prims.list)  ->  FStar_Syntax_Syntax.term = (fun t universe_of_binders -> (

let list_elements1 = (fun e -> (

let uu____18513 = (list_elements e)
in (match (uu____18513) with
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

let uu____18548 = (

let uu____18565 = (unmeta p)
in (FStar_All.pipe_right uu____18565 head_and_args))
in (match (uu____18548) with
| (head1, args) -> begin
(

let uu____18616 = (

let uu____18631 = (

let uu____18632 = (un_uinst head1)
in uu____18632.FStar_Syntax_Syntax.n)
in ((uu____18631), (args)))
in (match (uu____18616) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____18654, uu____18655))::(arg)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
arg
end
| uu____18707 -> begin
(

let uu____18722 = (

let uu____18728 = (

let uu____18730 = (tts p)
in (FStar_Util.format1 "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat\'s or a single SMTPatOr containing a list of lists of patterns" uu____18730))
in ((FStar_Errors.Error_IllSMTPat), (uu____18728)))
in (FStar_Errors.raise_error uu____18722 p.FStar_Syntax_Syntax.pos))
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____18773 = (

let uu____18790 = (unmeta t1)
in (FStar_All.pipe_right uu____18790 head_and_args))
in (match (uu____18773) with
| (head1, args) -> begin
(

let uu____18837 = (

let uu____18852 = (

let uu____18853 = (un_uinst head1)
in uu____18853.FStar_Syntax_Syntax.n)
in ((uu____18852), (args)))
in (match (uu____18837) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____18872))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____18909 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____18939 = (smt_pat_or1 t1)
in (match (uu____18939) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____18961 = (list_elements1 e)
in (FStar_All.pipe_right uu____18961 (FStar_List.map (fun branch1 -> (

let uu____18991 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____18991 (FStar_List.map one_pat)))))))
end
| uu____19020 -> begin
(

let uu____19025 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____19025)::[])
end))
end
| uu____19080 -> begin
(

let uu____19083 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____19083)::[])
end))))
in (

let uu____19138 = (

let uu____19171 = (

let uu____19172 = (FStar_Syntax_Subst.compress t)
in uu____19172.FStar_Syntax_Syntax.n)
in (match (uu____19171) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____19229 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____19229) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____19300; FStar_Syntax_Syntax.effect_name = uu____19301; FStar_Syntax_Syntax.result_typ = uu____19302; FStar_Syntax_Syntax.effect_args = ((pre, uu____19304))::((post, uu____19306))::((pats, uu____19308))::[]; FStar_Syntax_Syntax.flags = uu____19309}) -> begin
(

let uu____19370 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____19370)))
end
| uu____19407 -> begin
(failwith "impos")
end)
end))
end
| uu____19441 -> begin
(failwith "Impos")
end))
in (match (uu____19138) with
| (binders, pre, post, patterns) -> begin
(

let post1 = (unthunk_lemma_post post)
in (

let body = (

let uu____19533 = (

let uu____19540 = (

let uu____19541 = (

let uu____19548 = (mk_imp pre post1)
in (

let uu____19551 = (

let uu____19552 = (

let uu____19573 = (FStar_Syntax_Syntax.binders_to_names binders)
in ((uu____19573), (patterns)))
in FStar_Syntax_Syntax.Meta_pattern (uu____19552))
in ((uu____19548), (uu____19551))))
in FStar_Syntax_Syntax.Tm_meta (uu____19541))
in (FStar_Syntax_Syntax.mk uu____19540))
in (uu____19533 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let quant = (

let uu____19597 = (universe_of_binders binders)
in (FStar_List.fold_right2 (fun b u out -> (mk_forall u (FStar_Pervasives_Native.fst b) out)) binders uu____19597 body))
in quant)))
end))))))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____19627 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let is_layered : FStar_Syntax_Syntax.eff_decl  ->  Prims.bool = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Layered_eff (uu____19638) -> begin
true
end
| uu____19640 -> begin
false
end))


let is_dm4f : FStar_Syntax_Syntax.eff_decl  ->  Prims.bool = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.DM4F_eff (uu____19651) -> begin
true
end
| uu____19653 -> begin
false
end))


let apply_wp_eff_combinators : (FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme)  ->  FStar_Syntax_Syntax.wp_eff_combinators  ->  FStar_Syntax_Syntax.wp_eff_combinators = (fun f combs -> (

let uu____19671 = (f combs.FStar_Syntax_Syntax.ret_wp)
in (

let uu____19672 = (f combs.FStar_Syntax_Syntax.bind_wp)
in (

let uu____19673 = (f combs.FStar_Syntax_Syntax.stronger)
in (

let uu____19674 = (f combs.FStar_Syntax_Syntax.if_then_else)
in (

let uu____19675 = (f combs.FStar_Syntax_Syntax.ite_wp)
in (

let uu____19676 = (f combs.FStar_Syntax_Syntax.close_wp)
in (

let uu____19677 = (f combs.FStar_Syntax_Syntax.trivial)
in (

let uu____19678 = (FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr)
in (

let uu____19681 = (FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr)
in (

let uu____19684 = (FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr)
in {FStar_Syntax_Syntax.ret_wp = uu____19671; FStar_Syntax_Syntax.bind_wp = uu____19672; FStar_Syntax_Syntax.stronger = uu____19673; FStar_Syntax_Syntax.if_then_else = uu____19674; FStar_Syntax_Syntax.ite_wp = uu____19675; FStar_Syntax_Syntax.close_wp = uu____19676; FStar_Syntax_Syntax.trivial = uu____19677; FStar_Syntax_Syntax.repr = uu____19678; FStar_Syntax_Syntax.return_repr = uu____19681; FStar_Syntax_Syntax.bind_repr = uu____19684})))))))))))


let apply_layered_eff_combinators : (FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme)  ->  FStar_Syntax_Syntax.layered_eff_combinators  ->  FStar_Syntax_Syntax.layered_eff_combinators = (fun f combs -> (

let map_tuple = (fun uu____19716 -> (match (uu____19716) with
| (ts1, ts2) -> begin
(

let uu____19727 = (f ts1)
in (

let uu____19728 = (f ts2)
in ((uu____19727), (uu____19728))))
end))
in (

let uu____19729 = (map_tuple combs.FStar_Syntax_Syntax.l_repr)
in (

let uu____19734 = (map_tuple combs.FStar_Syntax_Syntax.l_return)
in (

let uu____19739 = (map_tuple combs.FStar_Syntax_Syntax.l_bind)
in (

let uu____19744 = (map_tuple combs.FStar_Syntax_Syntax.l_subcomp)
in (

let uu____19749 = (map_tuple combs.FStar_Syntax_Syntax.l_if_then_else)
in {FStar_Syntax_Syntax.l_base_effect = combs.FStar_Syntax_Syntax.l_base_effect; FStar_Syntax_Syntax.l_repr = uu____19729; FStar_Syntax_Syntax.l_return = uu____19734; FStar_Syntax_Syntax.l_bind = uu____19739; FStar_Syntax_Syntax.l_subcomp = uu____19744; FStar_Syntax_Syntax.l_if_then_else = uu____19749})))))))


let apply_eff_combinators : (FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme)  ->  FStar_Syntax_Syntax.eff_combinators  ->  FStar_Syntax_Syntax.eff_combinators = (fun f combs -> (match (combs) with
| FStar_Syntax_Syntax.Primitive_eff (combs1) -> begin
(

let uu____19771 = (apply_wp_eff_combinators f combs1)
in FStar_Syntax_Syntax.Primitive_eff (uu____19771))
end
| FStar_Syntax_Syntax.DM4F_eff (combs1) -> begin
(

let uu____19773 = (apply_wp_eff_combinators f combs1)
in FStar_Syntax_Syntax.DM4F_eff (uu____19773))
end
| FStar_Syntax_Syntax.Layered_eff (combs1) -> begin
(

let uu____19775 = (apply_layered_eff_combinators f combs1)
in FStar_Syntax_Syntax.Layered_eff (uu____19775))
end))


let get_wp_close_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
end
| uu____19790 -> begin
FStar_Pervasives_Native.None
end))


let get_eff_repr : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.repr
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.repr
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(

let uu____19804 = (FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19804 (fun _19811 -> FStar_Pervasives_Native.Some (_19811))))
end))


let get_bind_vc_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.bind_wp
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.bind_wp
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind FStar_Pervasives_Native.snd)
end))


let get_return_vc_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.ret_wp
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.ret_wp
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return FStar_Pervasives_Native.snd)
end))


let get_bind_repr : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.bind_repr
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.bind_repr
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(

let uu____19851 = (FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19851 (fun _19858 -> FStar_Pervasives_Native.Some (_19858))))
end))


let get_return_repr : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.return_repr
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.return_repr
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(

let uu____19872 = (FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19872 (fun _19879 -> FStar_Pervasives_Native.Some (_19879))))
end))


let get_wp_trivial_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial (fun _19893 -> FStar_Pervasives_Native.Some (_19893)))
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial (fun _19897 -> FStar_Pervasives_Native.Some (_19897)))
end
| uu____19898 -> begin
FStar_Pervasives_Native.None
end))


let get_layered_if_then_else_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(

let uu____19910 = (FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19910 (fun _19917 -> FStar_Pervasives_Native.Some (_19917))))
end
| uu____19918 -> begin
FStar_Pervasives_Native.None
end))


let get_wp_if_then_else_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else (fun _19932 -> FStar_Pervasives_Native.Some (_19932)))
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else (fun _19936 -> FStar_Pervasives_Native.Some (_19936)))
end
| uu____19937 -> begin
FStar_Pervasives_Native.None
end))


let get_wp_ite_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp (fun _19951 -> FStar_Pervasives_Native.Some (_19951)))
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp (fun _19955 -> FStar_Pervasives_Native.Some (_19955)))
end
| uu____19956 -> begin
FStar_Pervasives_Native.None
end))


let get_stronger_vc_combinator : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (combs) -> begin
combs.FStar_Syntax_Syntax.stronger
end
| FStar_Syntax_Syntax.DM4F_eff (combs) -> begin
combs.FStar_Syntax_Syntax.stronger
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp FStar_Pervasives_Native.snd)
end))


let get_stronger_repr : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Primitive_eff (uu____19980) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.DM4F_eff (uu____19981) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(

let uu____19983 = (FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____19983 (fun _19990 -> FStar_Pervasives_Native.Some (_19990))))
end))


let get_layered_effect_base : FStar_Syntax_Syntax.eff_decl  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun ed -> (match (ed.FStar_Syntax_Syntax.combinators) with
| FStar_Syntax_Syntax.Layered_eff (combs) -> begin
(FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_base_effect (fun _20004 -> FStar_Pervasives_Native.Some (_20004)))
end
| uu____20005 -> begin
FStar_Pervasives_Native.None
end))




