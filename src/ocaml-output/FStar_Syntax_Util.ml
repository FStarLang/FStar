
open Prims
open FStar_Pervasives

let tts_f : (FStar_Syntax_Syntax.term  ->  Prims.string) FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let tts : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let uu____32 = (FStar_ST.op_Bang tts_f)
in (match (uu____32) with
| FStar_Pervasives_Native.None -> begin
"<<hook unset>>"
end
| FStar_Pervasives_Native.Some (f) -> begin
(f t)
end)))


let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id1 -> (

let uu____87 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id1)::[])))
in (FStar_Ident.set_lid_range uu____87 id1.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (

let uu____93 = (

let uu____96 = (

let uu____99 = (FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (uu____99)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____96))
in (FStar_Ident.lid_of_ids uu____93)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____111 . (FStar_Syntax_Syntax.bv * 'Auu____111)  ->  (FStar_Syntax_Syntax.term * 'Auu____111) = (fun uu____124 -> (match (uu____124) with
| (b, imp) -> begin
(

let uu____131 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____131), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____182 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____182) with
| true -> begin
[]
end
| uu____197 -> begin
(

let uu____198 = (arg_of_non_null_binder b)
in (uu____198)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____232 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____314 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____314) with
| true -> begin
(

let b1 = (

let uu____338 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____338), ((FStar_Pervasives_Native.snd b))))
in (

let uu____345 = (arg_of_non_null_binder b1)
in ((b1), (uu____345))))
end
| uu____366 -> begin
(

let uu____367 = (arg_of_non_null_binder b)
in ((b), (uu____367)))
end)))))
in (FStar_All.pipe_right uu____232 FStar_List.unzip)))


let name_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____499 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____499) with
| true -> begin
(

let uu____506 = b
in (match (uu____506) with
| (a, imp) -> begin
(

let b1 = (

let uu____526 = (

let uu____527 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____527))
in (FStar_Ident.id_of_text uu____526))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____531 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____567 = (

let uu____574 = (

let uu____575 = (

let uu____590 = (name_binders binders)
in ((uu____590), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____575))
in (FStar_Syntax_Syntax.mk uu____574))
in (uu____567 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____612 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____648 -> (match (uu____648) with
| (t, imp) -> begin
(

let uu____659 = (

let uu____660 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____660))
in ((uu____659), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____714 -> (match (uu____714) with
| (t, imp) -> begin
(

let uu____731 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____731), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____743 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____743 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____754 . 'Auu____754  ->  'Auu____754 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____832 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____874 uu____875 -> (match (((uu____874), (uu____875))) with
| ((x, uu____901), (y, uu____903)) -> begin
(

let uu____924 = (

let uu____931 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____931)))
in FStar_Syntax_Syntax.NT (uu____924))
end)) replace_xs with_ys)
end
| uu____936 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____944) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____950, uu____951) -> begin
(unmeta e2)
end
| uu____992 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____1005) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____1012) -> begin
e1
end
| uu____1021 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1023, uu____1024) -> begin
(unmeta_safe e2)
end
| uu____1065 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____1079) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____1080) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____1090 = (univ_kernel u1)
in (match (uu____1090) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____1101) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____1108) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____1118 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____1118)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____1133), uu____1134) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____1135, FStar_Syntax_Syntax.U_bvar (uu____1136)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____1137) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1138, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____1139) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1140, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____1143), FStar_Syntax_Syntax.U_unif (uu____1144)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____1153), FStar_Syntax_Syntax.U_name (uu____1154)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____1181 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____1182 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____1181 - uu____1182)))
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
| uu____1209 -> begin
(

let copt = (

let uu____1213 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____1213 (fun uu____1228 -> (match (uu____1228) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1240 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____1242), uu____1243) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1246, FStar_Syntax_Syntax.U_max (uu____1247)) -> begin
(Prims.parse_int "1")
end
| uu____1250 -> begin
(

let uu____1255 = (univ_kernel u1)
in (match (uu____1255) with
| (k1, n1) -> begin
(

let uu____1262 = (univ_kernel u2)
in (match (uu____1262) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____1270 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____1281 = (compare_univs u1 u2)
in (Prims.op_Equality uu____1281 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (

let uu____1296 = (

let uu____1297 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = uu____1297; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp uu____1296)))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____1316) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____1325) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1347) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1356) -> begin
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

let uu____1382 = (

let uu____1383 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1383))
in {FStar_Syntax_Syntax.comp_univs = uu____1382; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1412 = (

let uu____1413 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1413))
in {FStar_Syntax_Syntax.comp_univs = uu____1412; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let uu___120_1448 = c
in (

let uu____1449 = (

let uu____1450 = (

let uu___121_1451 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___121_1451.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___121_1451.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___121_1451.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___121_1451.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1450))
in {FStar_Syntax_Syntax.n = uu____1449; FStar_Syntax_Syntax.pos = uu___120_1448.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_1448.FStar_Syntax_Syntax.vars})))


let lcomp_set_flags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun lc fs -> (

let comp_typ_set_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1476) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____1485) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___122_1496 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___122_1496.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___122_1496.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___122_1496.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___122_1496.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = fs})
in (

let uu___123_1497 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___123_1497.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___123_1497.FStar_Syntax_Syntax.vars}))
end))
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ fs (fun uu____1500 -> (

let uu____1501 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_typ_set_flags uu____1501))))))


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
| uu____1540 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1551) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1560) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___107_1581 -> (match (uu___107_1581) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1582 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___108_1591 -> (match (uu___108_1591) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1592 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___109_1601 -> (match (uu___109_1601) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1602 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___110_1615 -> (match (uu___110_1615) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1616 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___111_1625 -> (match (uu___111_1625) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1626 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1650) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1659) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___112_1672 -> (match (uu___112_1672) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1673 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_or_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> ((is_pure_effect l) || (is_ghost_effect l)))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___113_1706 -> (match (uu___113_1706) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1707 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1718 = (

let uu____1719 = (FStar_Syntax_Subst.compress t)
in uu____1719.FStar_Syntax_Syntax.n)
in (match (uu____1718) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1722, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1744 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1755 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1761 = (

let uu____1762 = (FStar_Syntax_Subst.compress t)
in uu____1762.FStar_Syntax_Syntax.n)
in (match (uu____1761) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1765, c) -> begin
(is_lemma_comp c)
end
| uu____1787 -> begin
false
end)))


let rec head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1793 = (

let uu____1794 = (FStar_Syntax_Subst.compress t)
in uu____1794.FStar_Syntax_Syntax.n)
in (match (uu____1793) with
| FStar_Syntax_Syntax.Tm_app (t1, uu____1798) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_match (t1, uu____1824) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_abs (uu____1861, t1, uu____1863) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1889, uu____1890) -> begin
(head_of t1)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1932) -> begin
(head_of t1)
end
| uu____1937 -> begin
t
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____2014 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____2095 = (head_and_args' head1)
in (match (uu____2095) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____2164 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____2190) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____2195 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2201 = (

let uu____2202 = (FStar_Syntax_Subst.compress t)
in uu____2202.FStar_Syntax_Syntax.n)
in (match (uu____2201) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2205, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____2231))::uu____2232 -> begin
(

let pats' = (unmeta pats)
in (

let uu____2292 = (head_and_args pats')
in (match (uu____2292) with
| (head1, uu____2310) -> begin
(

let uu____2335 = (

let uu____2336 = (un_uinst head1)
in uu____2336.FStar_Syntax_Syntax.n)
in (match (uu____2335) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____2340 -> begin
false
end))
end)))
end
| uu____2341 -> begin
false
end)
end
| uu____2352 -> begin
false
end)
end
| uu____2353 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___114_2367 -> (match (uu___114_2367) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2368 -> begin
false
end)))))
end
| uu____2369 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____2384) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____2394) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2422) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____2431) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___124_2443 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___124_2443.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___124_2443.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___124_2443.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___124_2443.FStar_Syntax_Syntax.flags}))
end))


let set_result_typ_lc : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____2456 -> (

let uu____2457 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (set_result_typ uu____2457 t)))))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___115_2472 -> (match (uu___115_2472) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2473 -> begin
false
end)))))


let comp_effect_args : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.args = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2479) -> begin
[]
end
| FStar_Syntax_Syntax.GTotal (uu____2496) -> begin
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
| uu____2533 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2541, uu____2542) -> begin
(unascribe e2)
end
| uu____2583 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2635, uu____2636) -> begin
(ascribe t' k)
end
| uu____2677 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2703 = (

let uu____2712 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2712))
in (uu____2703 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Subst.compress t)
in uu____2768.FStar_Syntax_Syntax.n)
in (match (uu____2767) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2772 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2772))
end
| uu____2773 -> begin
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
| (FStar_Syntax_Syntax.Lazy_sigelt, FStar_Syntax_Syntax.Lazy_sigelt) -> begin
true
end
| (FStar_Syntax_Syntax.Lazy_uvar, FStar_Syntax_Syntax.Lazy_uvar) -> begin
true
end
| uu____2784 -> begin
false
end))


let rec unlazy_as_t : 'Auu____2795 . FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.term  ->  'Auu____2795 = (fun k t -> (

let uu____2806 = (

let uu____2807 = (FStar_Syntax_Subst.compress t)
in uu____2807.FStar_Syntax_Syntax.n)
in (match (uu____2806) with
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k'; FStar_Syntax_Syntax.ltyp = uu____2812; FStar_Syntax_Syntax.rng = uu____2813}) when (eq_lazy_kind k k') -> begin
(FStar_Dyn.undyn v1)
end
| uu____2816 -> begin
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

let uu____2855 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2855; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.ltyp = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2867 = (

let uu____2882 = (unascribe t)
in (head_and_args' uu____2882))
in (match (uu____2867) with
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
| uu____2912 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____2918 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____2924 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___116_3048 -> (match (uu___116_3048) with
| true -> begin
Equal
end
| uu____3049 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___117_3055 -> (match (uu___117_3055) with
| true -> begin
Equal
end
| uu____3056 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____3073 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____3085) -> begin
NotEqual
end
| (uu____3086, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____3087) -> begin
Unknown
end
| (uu____3088, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____3110 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____3110) with
| true -> begin
(

let uu____3112 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____3189 -> (match (uu____3189) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____3230 = (eq_tm a1 a2)
in (eq_inj acc uu____3230))
end)) Equal) uu____3112))
end
| uu____3231 -> begin
NotEqual
end)))
in (

let uu____3232 = (

let uu____3237 = (

let uu____3238 = (unmeta t11)
in uu____3238.FStar_Syntax_Syntax.n)
in (

let uu____3241 = (

let uu____3242 = (unmeta t21)
in uu____3242.FStar_Syntax_Syntax.n)
in ((uu____3237), (uu____3241))))
in (match (uu____3232) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____3247), uu____3248) -> begin
(

let uu____3249 = (unlazy t11)
in (eq_tm uu____3249 t21))
end
| (uu____3250, FStar_Syntax_Syntax.Tm_lazy (uu____3251)) -> begin
(

let uu____3252 = (unlazy t21)
in (eq_tm t11 uu____3252))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))) with
| true -> begin
(equal_data f [] g [])
end
| uu____3277 -> begin
(

let uu____3278 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____3278))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____3291 = (eq_tm f g)
in (eq_and uu____3291 (fun uu____3294 -> (

let uu____3295 = (eq_univs_list us vs)
in (equal_if uu____3295)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3296)), uu____3297) -> begin
Unknown
end
| (uu____3298, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____3299))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____3302 = (FStar_Const.eq_const c d)
in (equal_iff uu____3302))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu____3304)), FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu____3306))) -> begin
(

let uu____3335 = (FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head)
in (equal_if uu____3335))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____3388 = (

let uu____3393 = (

let uu____3394 = (un_uinst h1)
in uu____3394.FStar_Syntax_Syntax.n)
in (

let uu____3397 = (

let uu____3398 = (un_uinst h2)
in uu____3398.FStar_Syntax_Syntax.n)
in ((uu____3393), (uu____3397))))
in (match (uu____3388) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((Prims.op_Equality f1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality f2.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
(equal_data f1 args1 f2 args2)
end
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____3410 = (

let uu____3411 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____3411))
in (FStar_List.mem uu____3410 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____3412 -> begin
(

let uu____3417 = (eq_tm h1 h2)
in (eq_and uu____3417 (fun uu____3419 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____3524 = (FStar_List.zip bs1 bs2)
in (

let uu____3587 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____3624 a -> (match (uu____3624) with
| (b1, b2) -> begin
(eq_and a (fun uu____3717 -> (branch_matches b1 b2)))
end)) uu____3524 uu____3587)))
end
| uu____3718 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____3721 = (eq_univs u v1)
in (equal_if uu____3721))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(

let uu____3734 = (eq_quoteinfo q1 q2)
in (eq_and uu____3734 (fun uu____3736 -> (eq_tm t12 t22))))
end
| (FStar_Syntax_Syntax.Tm_refine (t12, phi1), FStar_Syntax_Syntax.Tm_refine (t22, phi2)) -> begin
(

let uu____3749 = (eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort)
in (eq_and uu____3749 (fun uu____3751 -> (eq_tm phi1 phi2))))
end
| uu____3752 -> begin
Unknown
end))))))))))
and eq_quoteinfo : FStar_Syntax_Syntax.quoteinfo  ->  FStar_Syntax_Syntax.quoteinfo  ->  eq_result = (fun q1 q2 -> (match ((Prims.op_disEquality q1.FStar_Syntax_Syntax.qkind q2.FStar_Syntax_Syntax.qkind)) with
| true -> begin
NotEqual
end
| uu____3759 -> begin
(eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes q2.FStar_Syntax_Syntax.antiquotes)
end))
and eq_antiquotes : (FStar_Syntax_Syntax.bv * Prims.bool * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Syntax_Syntax.bv * Prims.bool * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| ([], uu____3838) -> begin
NotEqual
end
| (uu____3877, []) -> begin
NotEqual
end
| (((x1, b1, t1))::a11, ((x2, b2, t2))::a21) -> begin
(match ((not (((FStar_Syntax_Syntax.bv_eq x1 x2) && (Prims.op_Equality b1 b2))))) with
| true -> begin
NotEqual
end
| uu____3988 -> begin
(

let uu____3989 = (eq_tm t1 t2)
in (match (uu____3989) with
| NotEqual -> begin
NotEqual
end
| Unknown -> begin
(

let uu____3990 = (eq_antiquotes a11 a21)
in (match (uu____3990) with
| NotEqual -> begin
NotEqual
end
| uu____3991 -> begin
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
| (FStar_Pervasives_Native.None, uu____4006) -> begin
NotEqual
end
| (uu____4013, FStar_Pervasives_Native.None) -> begin
NotEqual
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b1)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b2))) when (Prims.op_Equality b1 b2) -> begin
Equal
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t1)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t2))) -> begin
(eq_tm t1 t2)
end
| uu____4036 -> begin
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
| (uu____4123, uu____4124) -> begin
false
end))
in (

let uu____4133 = b1
in (match (uu____4133) with
| (p1, w1, t1) -> begin
(

let uu____4167 = b2
in (match (uu____4167) with
| (p2, w2, t2) -> begin
(

let uu____4201 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____4201) with
| true -> begin
(

let uu____4202 = ((

let uu____4205 = (eq_tm t1 t2)
in (Prims.op_Equality uu____4205 Equal)) && (related_by (fun t11 t21 -> (

let uu____4214 = (eq_tm t11 t21)
in (Prims.op_Equality uu____4214 Equal))) w1 w2))
in (match (uu____4202) with
| true -> begin
Equal
end
| uu____4215 -> begin
Unknown
end))
end
| uu____4216 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____4276))::a11, ((b, uu____4279))::b1) -> begin
(

let uu____4353 = (eq_tm a b)
in (match (uu____4353) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____4354 -> begin
Unknown
end))
end
| uu____4355 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____4389) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4395, uu____4396) -> begin
(unrefine t2)
end
| uu____4437 -> begin
t1
end)))


let rec is_uvar : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4443 = (

let uu____4444 = (FStar_Syntax_Subst.compress t)
in uu____4444.FStar_Syntax_Syntax.n)
in (match (uu____4443) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4447) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4461) -> begin
(is_uvar t1)
end
| FStar_Syntax_Syntax.Tm_app (uu____4466) -> begin
(

let uu____4483 = (

let uu____4484 = (FStar_All.pipe_right t head_and_args)
in (FStar_All.pipe_right uu____4484 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____4483 is_uvar))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4546, uu____4547) -> begin
(is_uvar t1)
end
| uu____4588 -> begin
false
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4594 = (

let uu____4595 = (unrefine t)
in uu____4595.FStar_Syntax_Syntax.n)
in (match (uu____4594) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4600) -> begin
(is_unit t1)
end
| uu____4605 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4611 = (

let uu____4612 = (unrefine t)
in uu____4612.FStar_Syntax_Syntax.n)
in (match (uu____4611) with
| FStar_Syntax_Syntax.Tm_type (uu____4615) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____4618) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____4644) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____4649, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____4671 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____4677 = (

let uu____4678 = (FStar_Syntax_Subst.compress e)
in uu____4678.FStar_Syntax_Syntax.n)
in (match (uu____4677) with
| FStar_Syntax_Syntax.Tm_abs (uu____4681) -> begin
true
end
| uu____4700 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4706 = (

let uu____4707 = (FStar_Syntax_Subst.compress t)
in uu____4707.FStar_Syntax_Syntax.n)
in (match (uu____4706) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4710) -> begin
true
end
| uu____4725 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____4733) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4739, uu____4740) -> begin
(pre_typ t2)
end
| uu____4781 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____4805 = (

let uu____4806 = (un_uinst typ1)
in uu____4806.FStar_Syntax_Syntax.n)
in (match (uu____4805) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____4871 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____4901 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____4921, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____4928) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____4933, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4944, uu____4945, uu____4946, uu____4947, uu____4948) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____4958, uu____4959, uu____4960, uu____4961) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____4967, uu____4968, uu____4969, uu____4970, uu____4971) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____4977, uu____4978) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____4980, uu____4981) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____4984) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____4985) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____4986) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____4999 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___118_5022 -> (match (uu___118_5022) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____5035 'Auu____5036 . ('Auu____5035 FStar_Syntax_Syntax.syntax * 'Auu____5036)  ->  FStar_Range.range = (fun uu____5047 -> (match (uu____5047) with
| (hd1, uu____5055) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____5068 'Auu____5069 . ('Auu____5068 FStar_Syntax_Syntax.syntax * 'Auu____5069) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____5166 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_app_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f bs -> (

let uu____5224 = (FStar_List.map (fun uu____5251 -> (match (uu____5251) with
| (bv, aq) -> begin
(

let uu____5270 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5270), (aq)))
end)) bs)
in (mk_app f uu____5224)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____5319 = (FStar_Ident.range_of_lid l)
in (

let uu____5320 = (

let uu____5329 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____5329))
in (uu____5320 FStar_Pervasives_Native.None uu____5319)))
end
| uu____5337 -> begin
(

let e = (

let uu____5351 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____5351 args))
in (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____5366 = (

let uu____5371 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____5371), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____5366))
end
| uu____5372 -> begin
x
end))


let field_projector_prefix : Prims.string = "__proj__"


let field_projector_sep : Prims.string = "__item__"


let field_projector_contains_constructor : Prims.string  ->  Prims.bool = (fun s -> (FStar_Util.starts_with s field_projector_prefix))


let mk_field_projector_name_from_string : Prims.string  ->  Prims.string  ->  Prims.string = (fun constr field -> (Prims.strcat field_projector_prefix (Prims.strcat constr (Prims.strcat field_projector_sep field))))


let mk_field_projector_name_from_ident : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid i -> (

let j = (unmangle_field_name i)
in (

let jtext = j.FStar_Ident.idText
in (

let newi = (match ((field_projector_contains_constructor jtext)) with
| true -> begin
j
end
| uu____5401 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____5422 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5422) with
| true -> begin
(

let uu____5423 = (

let uu____5428 = (

let uu____5429 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____5429))
in (

let uu____5430 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____5428), (uu____5430))))
in (FStar_Ident.mk_ident uu____5423))
end
| uu____5431 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___125_5433 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___125_5433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___125_5433.FStar_Syntax_Syntax.sort})
in (

let uu____5434 = (mk_field_projector_name_from_ident lid nm)
in ((uu____5434), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____5445) -> begin
ses
end
| uu____5454 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____5463 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____5474 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____5474) with
| FStar_Pervasives_Native.Some (uu____5477) -> begin
(

let uu____5478 = (

let uu____5479 = (

let uu____5480 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____5480))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5479))
in (failwith uu____5478))
end
| uu____5481 -> begin
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
| uu____5556 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____5601 = (

let uu___126_5602 = rc
in (

let uu____5603 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___126_5602.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5603; FStar_Syntax_Syntax.residual_flags = uu___126_5602.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____5601))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____5620 -> begin
(

let body = (

let uu____5622 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____5622))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____5656 = (

let uu____5663 = (

let uu____5664 = (

let uu____5683 = (

let uu____5692 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____5692 bs'))
in (

let uu____5707 = (close_lopt lopt')
in ((uu____5683), (t1), (uu____5707))))
in FStar_Syntax_Syntax.Tm_abs (uu____5664))
in (FStar_Syntax_Syntax.mk uu____5663))
in (uu____5656 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____5725 -> begin
(

let uu____5732 = (

let uu____5739 = (

let uu____5740 = (

let uu____5759 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____5768 = (close_lopt lopt)
in ((uu____5759), (body), (uu____5768))))
in FStar_Syntax_Syntax.Tm_abs (uu____5740))
in (FStar_Syntax_Syntax.mk uu____5739))
in (uu____5732 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____5826 -> begin
(

let uu____5835 = (

let uu____5842 = (

let uu____5843 = (

let uu____5858 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____5867 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____5858), (uu____5867))))
in FStar_Syntax_Syntax.Tm_arrow (uu____5843))
in (FStar_Syntax_Syntax.mk uu____5842))
in (uu____5835 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____5918 = (

let uu____5919 = (FStar_Syntax_Subst.compress t)
in uu____5919.FStar_Syntax_Syntax.n)
in (match (uu____5918) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____5949) -> begin
(

let uu____5958 = (

let uu____5959 = (FStar_Syntax_Subst.compress tres)
in uu____5959.FStar_Syntax_Syntax.n)
in (match (uu____5958) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____6002 -> begin
t
end))
end
| uu____6003 -> begin
t
end)
end
| uu____6004 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____6021 = (

let uu____6022 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____6022 t.FStar_Syntax_Syntax.pos))
in (

let uu____6023 = (

let uu____6030 = (

let uu____6031 = (

let uu____6038 = (

let uu____6041 = (

let uu____6042 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____6042)::[])
in (FStar_Syntax_Subst.close uu____6041 t))
in ((b), (uu____6038)))
in FStar_Syntax_Syntax.Tm_refine (uu____6031))
in (FStar_Syntax_Syntax.mk uu____6030))
in (uu____6023 FStar_Pervasives_Native.None uu____6021))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6123 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6123) with
| (bs1, c1) -> begin
(

let uu____6142 = (is_total_comp c1)
in (match (uu____6142) with
| true -> begin
(

let uu____6155 = (arrow_formals_comp (comp_result c1))
in (match (uu____6155) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____6212 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6221; FStar_Syntax_Syntax.index = uu____6222; FStar_Syntax_Syntax.sort = k2}, uu____6224) -> begin
(arrow_formals_comp k2)
end
| uu____6231 -> begin
(

let uu____6232 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____6232)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____6266 = (arrow_formals_comp k)
in (match (uu____6266) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let let_rec_arity : FStar_Syntax_Syntax.letbinding  ->  (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option) = (fun lb -> (

let rec arrow_until_decreases = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6403 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6403) with
| (bs1, c1) -> begin
(

let ct = (comp_to_comp_typ c1)
in (

let uu____6427 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.find_opt (fun uu___119_6436 -> (match (uu___119_6436) with
| FStar_Syntax_Syntax.DECREASES (uu____6437) -> begin
true
end
| uu____6440 -> begin
false
end))))
in (match (uu____6427) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (d)) -> begin
((bs1), (FStar_Pervasives_Native.Some (d)))
end
| uu____6474 -> begin
(

let uu____6477 = (is_total_comp c1)
in (match (uu____6477) with
| true -> begin
(

let uu____6494 = (arrow_until_decreases (comp_result c1))
in (match (uu____6494) with
| (bs', d) -> begin
(((FStar_List.append bs1 bs')), (d))
end))
end
| uu____6571 -> begin
((bs1), (FStar_Pervasives_Native.None))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6586; FStar_Syntax_Syntax.index = uu____6587; FStar_Syntax_Syntax.sort = k2}, uu____6589) -> begin
(arrow_until_decreases k2)
end
| uu____6596 -> begin
(([]), (FStar_Pervasives_Native.None))
end)))
in (

let uu____6617 = (arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____6617) with
| (bs, dopt) -> begin
(

let n_univs = (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs)
in (

let uu____6669 = (FStar_Util.map_opt dopt (fun d -> (

let d_bvs = (FStar_Syntax_Free.names d)
in (

let uu____6688 = (FStar_Common.tabulate n_univs (fun uu____6696 -> false))
in (

let uu____6697 = (FStar_All.pipe_right bs (FStar_List.map (fun uu____6719 -> (match (uu____6719) with
| (x, uu____6727) -> begin
(FStar_Util.set_mem x d_bvs)
end))))
in (FStar_List.append uu____6688 uu____6697))))))
in (((n_univs + (FStar_List.length bs))), (uu____6669))))
end))))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____6785 = (

let uu___127_6786 = rc
in (

let uu____6787 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___127_6786.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6787; FStar_Syntax_Syntax.residual_flags = uu___127_6786.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____6785))
end
| uu____6796 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____6830 = (

let uu____6831 = (

let uu____6834 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____6834))
in uu____6831.FStar_Syntax_Syntax.n)
in (match (uu____6830) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____6880 = (aux t2 what)
in (match (uu____6880) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____6952 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____6969 = (aux t FStar_Pervasives_Native.None)
in (match (uu____6969) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____7017 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____7017) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____7178) -> begin
def
end
| (uu____7189, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____7201) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_4 -> FStar_Syntax_Syntax.U_name (_0_4))))
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

let uu____7297 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____7297) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____7332 -> begin
(

let t' = (arrow binders c)
in (

let uu____7344 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____7344) with
| (uvs1, t'1) -> begin
(

let uu____7365 = (

let uu____7366 = (FStar_Syntax_Subst.compress t'1)
in uu____7366.FStar_Syntax_Syntax.n)
in (match (uu____7365) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____7415 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____7436 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____7443 -> begin
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

let uu____7491 = (

let uu____7492 = (pre_typ t)
in uu____7492.FStar_Syntax_Syntax.n)
in (match (uu____7491) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____7496 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____7507 = (

let uu____7508 = (pre_typ t)
in uu____7508.FStar_Syntax_Syntax.n)
in (match (uu____7507) with
| FStar_Syntax_Syntax.Tm_fvar (uu____7511) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____7513) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____7539) -> begin
(is_constructed_typ t1 lid)
end
| uu____7544 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____7555) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____7556) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____7557) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____7559) -> begin
(get_tycon t2)
end
| uu____7584 -> begin
FStar_Pervasives_Native.None
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7590 = (

let uu____7591 = (un_uinst t)
in uu____7591.FStar_Syntax_Syntax.n)
in (match (uu____7590) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____7595 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____7602 = (

let uu____7605 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____7605))
in (match (uu____7602) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____7618 -> begin
false
end))
end
| uu____7621 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____7630 -> (

let u = (

let uu____7636 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_5 -> FStar_Syntax_Syntax.U_unif (_0_5)) uu____7636))
in (

let uu____7653 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____7653), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____7664 = (eq_tm a a')
in (match (uu____7664) with
| Equal -> begin
true
end
| uu____7665 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____7668 = (

let uu____7675 = (

let uu____7676 = (

let uu____7677 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____7677 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____7676))
in (FStar_Syntax_Syntax.mk uu____7675))
in (uu____7668 FStar_Pervasives_Native.None FStar_Range.dummyRange))


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


let t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____7752 = (

let uu____7755 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____7756 = (

let uu____7763 = (

let uu____7764 = (

let uu____7781 = (

let uu____7792 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____7801 = (

let uu____7812 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____7812)::[])
in (uu____7792)::uu____7801))
in ((tand), (uu____7781)))
in FStar_Syntax_Syntax.Tm_app (uu____7764))
in (FStar_Syntax_Syntax.mk uu____7763))
in (uu____7756 FStar_Pervasives_Native.None uu____7755)))
in FStar_Pervasives_Native.Some (uu____7752))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____7891 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____7892 = (

let uu____7899 = (

let uu____7900 = (

let uu____7917 = (

let uu____7928 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____7937 = (

let uu____7948 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____7948)::[])
in (uu____7928)::uu____7937))
in ((op_t), (uu____7917)))
in FStar_Syntax_Syntax.Tm_app (uu____7900))
in (FStar_Syntax_Syntax.mk uu____7899))
in (uu____7892 FStar_Pervasives_Native.None uu____7891))))


let mk_neg : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____8007 = (

let uu____8014 = (

let uu____8015 = (

let uu____8032 = (

let uu____8043 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____8043)::[])
in ((t_not), (uu____8032)))
in FStar_Syntax_Syntax.Tm_app (uu____8015))
in (FStar_Syntax_Syntax.mk uu____8014))
in (uu____8007 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


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

let uu____8236 = (

let uu____8243 = (

let uu____8244 = (

let uu____8261 = (

let uu____8272 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8272)::[])
in ((b2t_v), (uu____8261)))
in FStar_Syntax_Syntax.Tm_app (uu____8244))
in (FStar_Syntax_Syntax.mk uu____8243))
in (uu____8236 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let is_t_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____8317 = (

let uu____8318 = (unmeta t)
in uu____8318.FStar_Syntax_Syntax.n)
in (match (uu____8317) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____8322 -> begin
false
end)))


let mk_conj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____8343 = (is_t_true t1)
in (match (uu____8343) with
| true -> begin
t2
end
| uu____8346 -> begin
(

let uu____8347 = (is_t_true t2)
in (match (uu____8347) with
| true -> begin
t1
end
| uu____8350 -> begin
(mk_conj t1 t2)
end))
end)))


let mk_disj_simp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let uu____8371 = (is_t_true t1)
in (match (uu____8371) with
| true -> begin
t_true
end
| uu____8374 -> begin
(

let uu____8375 = (is_t_true t2)
in (match (uu____8375) with
| true -> begin
t_true
end
| uu____8378 -> begin
(mk_disj t1 t2)
end))
end)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____8399 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____8400 = (

let uu____8407 = (

let uu____8408 = (

let uu____8425 = (

let uu____8436 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____8445 = (

let uu____8456 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____8456)::[])
in (uu____8436)::uu____8445))
in ((teq), (uu____8425)))
in FStar_Syntax_Syntax.Tm_app (uu____8408))
in (FStar_Syntax_Syntax.mk uu____8407))
in (uu____8400 FStar_Pervasives_Native.None uu____8399))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____8525 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____8526 = (

let uu____8533 = (

let uu____8534 = (

let uu____8551 = (

let uu____8562 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____8571 = (

let uu____8582 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____8591 = (

let uu____8602 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____8602)::[])
in (uu____8582)::uu____8591))
in (uu____8562)::uu____8571))
in ((eq_inst), (uu____8551)))
in FStar_Syntax_Syntax.Tm_app (uu____8534))
in (FStar_Syntax_Syntax.mk uu____8533))
in (uu____8526 FStar_Pervasives_Native.None uu____8525)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____8681 = (

let uu____8688 = (

let uu____8689 = (

let uu____8706 = (

let uu____8717 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____8726 = (

let uu____8737 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____8746 = (

let uu____8757 = (FStar_Syntax_Syntax.as_arg t')
in (uu____8757)::[])
in (uu____8737)::uu____8746))
in (uu____8717)::uu____8726))
in ((t_has_type1), (uu____8706)))
in FStar_Syntax_Syntax.Tm_app (uu____8689))
in (FStar_Syntax_Syntax.mk uu____8688))
in (uu____8681 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____8836 = (

let uu____8843 = (

let uu____8844 = (

let uu____8861 = (

let uu____8872 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____8881 = (

let uu____8892 = (FStar_Syntax_Syntax.as_arg e)
in (uu____8892)::[])
in (uu____8872)::uu____8881))
in ((t_with_type1), (uu____8861)))
in FStar_Syntax_Syntax.Tm_app (uu____8844))
in (FStar_Syntax_Syntax.mk uu____8843))
in (uu____8836 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (

let uu____8940 = (

let uu____8947 = (

let uu____8948 = (

let uu____8955 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____8955), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____8948))
in (FStar_Syntax_Syntax.mk uu____8947))
in (uu____8940 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____8968 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____8981) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____8992) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____8968) with
| (eff_name, flags1) -> begin
(FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1 (fun uu____9013 -> c0))
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____9091 = (

let uu____9098 = (

let uu____9099 = (

let uu____9116 = (

let uu____9127 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____9136 = (

let uu____9147 = (

let uu____9156 = (

let uu____9157 = (

let uu____9158 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9158)::[])
in (abs uu____9157 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____9156))
in (uu____9147)::[])
in (uu____9127)::uu____9136))
in ((fa), (uu____9116)))
in FStar_Syntax_Syntax.Tm_app (uu____9099))
in (FStar_Syntax_Syntax.mk uu____9098))
in (uu____9091 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____9285 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____9285) with
| true -> begin
f1
end
| uu____9286 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____9298) -> begin
true
end
| uu____9299 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____9344 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____9344), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____9372 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____9372), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____9385 = (

let uu____9386 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____9386))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____9385)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____9460 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____9463 = (

let uu____9474 = (FStar_Syntax_Syntax.as_arg p)
in (uu____9474)::[])
in (mk_app uu____9460 uu____9463)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____9512 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____9515 = (

let uu____9526 = (FStar_Syntax_Syntax.as_arg p)
in (uu____9526)::[])
in (mk_app uu____9512 uu____9515)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____9560 = (head_and_args t)
in (match (uu____9560) with
| (head1, args) -> begin
(

let uu____9607 = (

let uu____9622 = (

let uu____9623 = (un_uinst head1)
in uu____9623.FStar_Syntax_Syntax.n)
in ((uu____9622), (args)))
in (match (uu____9607) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____9642))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____9708 = (

let uu____9713 = (

let uu____9714 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____9714)::[])
in (FStar_Syntax_Subst.open_term uu____9713 p))
in (match (uu____9708) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9771 -> begin
(failwith "impossible")
end)
in (

let uu____9778 = (

let uu____9779 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____9779))
in (match (uu____9778) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9790 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____9793 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____9796 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____9826 = (head_and_args t)
in (match (uu____9826) with
| (head1, args) -> begin
(

let uu____9877 = (

let uu____9892 = (

let uu____9893 = (FStar_Syntax_Subst.compress head1)
in uu____9893.FStar_Syntax_Syntax.n)
in ((uu____9892), (args)))
in (match (uu____9877) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9915; FStar_Syntax_Syntax.vars = uu____9916}, (u)::[]), ((t1, uu____9919))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____9966 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____10000 = (head_and_args t)
in (match (uu____10000) with
| (head1, args) -> begin
(

let uu____10051 = (

let uu____10066 = (

let uu____10067 = (FStar_Syntax_Subst.compress head1)
in uu____10067.FStar_Syntax_Syntax.n)
in ((uu____10066), (args)))
in (match (uu____10051) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10089; FStar_Syntax_Syntax.vars = uu____10090}, (u)::[]), ((t1, uu____10093))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____10140 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____10166 = (

let uu____10183 = (unmeta t)
in (head_and_args uu____10183))
in (match (uu____10166) with
| (head1, uu____10185) -> begin
(

let uu____10210 = (

let uu____10211 = (un_uinst head1)
in uu____10211.FStar_Syntax_Syntax.n)
in (match (uu____10210) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____10215 -> begin
false
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____10233 = (

let uu____10246 = (

let uu____10247 = (FStar_Syntax_Subst.compress t)
in uu____10247.FStar_Syntax_Syntax.n)
in (match (uu____10246) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____10376 = (

let uu____10387 = (

let uu____10388 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____10388))
in ((b), (uu____10387)))
in FStar_Pervasives_Native.Some (uu____10376))
end
| uu____10405 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____10233 (fun uu____10443 -> (match (uu____10443) with
| (b, c) -> begin
(

let uu____10480 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____10480) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____10543 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____10576 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____10576)))


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
| uu____10624 -> begin
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
| uu____10662 -> begin
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
| uu____10698 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____10735)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____10747)) -> begin
(unmeta_monadic t)
end
| uu____10760 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____10844 -> (match (uu____10844) with
| (lid, arity) -> begin
(

let uu____10853 = (

let uu____10870 = (unmeta_monadic f2)
in (head_and_args uu____10870))
in (match (uu____10853) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____10900 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____10900) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____10915 -> begin
FStar_Pervasives_Native.None
end)))
end))
end))
in (FStar_Util.find_map connectives (aux f1)))))
in (

let patterns = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____10977 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____10977)))
end
| uu____10990 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____11032 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____11051 = (head_and_args t1)
in (match (uu____11051) with
| (t2, args) -> begin
(

let uu____11106 = (un_uinst t2)
in (

let uu____11107 = (FStar_All.pipe_right args (FStar_List.map (fun uu____11148 -> (match (uu____11148) with
| (t3, imp) -> begin
(

let uu____11167 = (unascribe t3)
in ((uu____11167), (imp)))
end))))
in ((uu____11106), (uu____11107))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____11216 = (

let uu____11239 = (flat t1)
in ((qopt), (uu____11239)))
in (match (uu____11216) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____11278; FStar_Syntax_Syntax.vars = uu____11279}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____11282); FStar_Syntax_Syntax.pos = uu____11283; FStar_Syntax_Syntax.vars = uu____11284}, uu____11285))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____11384; FStar_Syntax_Syntax.vars = uu____11385}, (uu____11386)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____11389); FStar_Syntax_Syntax.pos = uu____11390; FStar_Syntax_Syntax.vars = uu____11391}, uu____11392))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____11506; FStar_Syntax_Syntax.vars = uu____11507}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____11510); FStar_Syntax_Syntax.pos = uu____11511; FStar_Syntax_Syntax.vars = uu____11512}, uu____11513))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____11604 = (

let uu____11607 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____11607))
in (aux uu____11604 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____11615; FStar_Syntax_Syntax.vars = uu____11616}, (uu____11617)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____11620); FStar_Syntax_Syntax.pos = uu____11621; FStar_Syntax_Syntax.vars = uu____11622}, uu____11623))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____11730 = (

let uu____11733 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____11733))
in (aux uu____11730 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____11741) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____11791 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____11791) with
| (bs1, t2) -> begin
(

let uu____11800 = (patterns t2)
in (match (uu____11800) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____11847 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____11848 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____11924 = (un_squash t)
in (FStar_Util.bind_opt uu____11924 (fun t1 -> (

let uu____11940 = (head_and_args' t1)
in (match (uu____11940) with
| (hd1, args) -> begin
(

let uu____11979 = (

let uu____11984 = (

let uu____11985 = (un_uinst hd1)
in uu____11985.FStar_Syntax_Syntax.n)
in ((uu____11984), ((FStar_List.length args))))
in (match (uu____11979) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_6) when ((_0_6 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_and_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.and_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_7) when ((_0_7 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_or_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.or_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_8) when ((_0_8 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_9) when ((_0_9 = (Prims.parse_int "3")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_10) when ((_0_10 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_11) when ((_0_11 = (Prims.parse_int "4")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_12) when ((_0_12 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_true_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.true_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_13) when ((_0_13 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_false_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.false_lid), (args))))
end
| uu____12006 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____12035 = (un_squash t)
in (FStar_Util.bind_opt uu____12035 (fun t1 -> (

let uu____12050 = (arrow_one t1)
in (match (uu____12050) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____12065 = (

let uu____12066 = (is_tot_or_gtot_comp c)
in (not (uu____12066)))
in (match (uu____12065) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____12069 -> begin
(

let q = (

let uu____12073 = (comp_to_comp_typ_nouniv c)
in uu____12073.FStar_Syntax_Syntax.result_typ)
in (

let uu____12074 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____12074) with
| true -> begin
(

let uu____12079 = (patterns q)
in (match (uu____12079) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____12140 -> begin
(

let uu____12141 = (

let uu____12142 = (

let uu____12147 = (

let uu____12148 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____12159 = (

let uu____12170 = (FStar_Syntax_Syntax.as_arg q)
in (uu____12170)::[])
in (uu____12148)::uu____12159))
in ((FStar_Parser_Const.imp_lid), (uu____12147)))
in BaseConn (uu____12142))
in FStar_Pervasives_Native.Some (uu____12141))
end)))
end))
end
| uu____12203 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____12211 = (un_squash t)
in (FStar_Util.bind_opt uu____12211 (fun t1 -> (

let uu____12242 = (head_and_args' t1)
in (match (uu____12242) with
| (hd1, args) -> begin
(

let uu____12281 = (

let uu____12296 = (

let uu____12297 = (un_uinst hd1)
in uu____12297.FStar_Syntax_Syntax.n)
in ((uu____12296), (args)))
in (match (uu____12281) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____12314))::((a2, uu____12316))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____12367 = (

let uu____12368 = (FStar_Syntax_Subst.compress a2)
in uu____12368.FStar_Syntax_Syntax.n)
in (match (uu____12367) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____12375) -> begin
(

let uu____12410 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____12410) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____12463 -> begin
(failwith "impossible")
end)
in (

let uu____12470 = (patterns q1)
in (match (uu____12470) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____12531 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____12532 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____12555 = (destruct_sq_forall phi)
in (match (uu____12555) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____12571 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____12577 = (destruct_sq_exists phi)
in (match (uu____12577) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____12593 -> begin
f1
end))
end
| uu____12596 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____12600 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____12600 (fun uu____12605 -> (

let uu____12606 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____12606 (fun uu____12611 -> (

let uu____12612 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____12612 (fun uu____12617 -> (

let uu____12618 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____12618 (fun uu____12623 -> (

let uu____12624 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____12624 (fun uu____12628 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let unthunk_lemma_post : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____12640 = (

let uu____12641 = (FStar_Syntax_Subst.compress t)
in uu____12641.FStar_Syntax_Syntax.n)
in (match (uu____12640) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____12648) -> begin
(

let uu____12683 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____12683) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____12717 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____12717) with
| true -> begin
(

let uu____12722 = (

let uu____12733 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____12733)::[])
in (mk_app t uu____12722))
end
| uu____12758 -> begin
e1
end)))
end))
end
| uu____12759 -> begin
(

let uu____12760 = (

let uu____12771 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____12771)::[])
in (mk_app t uu____12760))
end)))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____12812 = (

let uu____12817 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____12817))
in (

let uu____12818 = (

let uu____12819 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____12819))
in (

let uu____12822 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____12812 a.FStar_Syntax_Syntax.action_univs uu____12818 FStar_Parser_Const.effect_Tot_lid uu____12822 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____12845 = (

let uu____12852 = (

let uu____12853 = (

let uu____12870 = (

let uu____12881 = (FStar_Syntax_Syntax.as_arg t)
in (uu____12881)::[])
in ((reify_1), (uu____12870)))
in FStar_Syntax_Syntax.Tm_app (uu____12853))
in (FStar_Syntax_Syntax.mk uu____12852))
in (uu____12845 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12927) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____12951 = (unfold_lazy i)
in (delta_qualifier uu____12951))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____12953) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____12954) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____12955) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____12978) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____12991) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____12992) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____12999) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____13000) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____13016) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____13021; FStar_Syntax_Syntax.index = uu____13022; FStar_Syntax_Syntax.sort = t2}, uu____13024) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____13032) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____13038, uu____13039) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____13081) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____13106, t2, uu____13108) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____13133, t2) -> begin
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

let uu____13164 = (delta_qualifier t)
in (incr_delta_depth uu____13164)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____13170 = (

let uu____13171 = (FStar_Syntax_Subst.compress t)
in uu____13171.FStar_Syntax_Syntax.n)
in (match (uu____13170) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____13174 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____13188 = (

let uu____13205 = (unmeta e)
in (head_and_args uu____13205))
in (match (uu____13188) with
| (head1, args) -> begin
(

let uu____13236 = (

let uu____13251 = (

let uu____13252 = (un_uinst head1)
in uu____13252.FStar_Syntax_Syntax.n)
in ((uu____13251), (args)))
in (match (uu____13236) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____13270) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____13294)::((hd1, uu____13296))::((tl1, uu____13298))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____13365 = (

let uu____13368 = (

let uu____13371 = (list_elements tl1)
in (FStar_Util.must uu____13371))
in (hd1)::uu____13368)
in FStar_Pervasives_Native.Some (uu____13365))
end
| uu____13380 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____13403 . ('Auu____13403  ->  'Auu____13403)  ->  'Auu____13403 Prims.list  ->  'Auu____13403 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____13428 = (f a)
in (uu____13428)::[])
end
| (x)::xs -> begin
(

let uu____13433 = (apply_last f xs)
in (x)::uu____13433)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____13479 = (

let uu____13486 = (

let uu____13487 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____13487))
in (FStar_Syntax_Syntax.mk uu____13486))
in (uu____13479 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____13504 = (

let uu____13509 = (

let uu____13510 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____13510 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____13509 args))
in (uu____13504 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____13526 = (

let uu____13531 = (

let uu____13532 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____13532 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____13531 args))
in (uu____13526 FStar_Pervasives_Native.None pos)))
in (

let uu____13535 = (

let uu____13536 = (

let uu____13537 = (FStar_Syntax_Syntax.iarg typ)
in (uu____13537)::[])
in (nil uu____13536 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____13571 = (

let uu____13572 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____13581 = (

let uu____13592 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____13601 = (

let uu____13612 = (FStar_Syntax_Syntax.as_arg a)
in (uu____13612)::[])
in (uu____13592)::uu____13601))
in (uu____13572)::uu____13581))
in (cons1 uu____13571 t.FStar_Syntax_Syntax.pos))) l uu____13535))))))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____13716 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____13823 -> begin
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
| uu____13978 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____14010 -> begin
((

let uu____14012 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____14012) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____14032 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____14204 = (unmeta_safe t1)
in (canon_app uu____14204))
in (

let t21 = (

let uu____14210 = (unmeta_safe t2)
in (canon_app uu____14210))
in (

let uu____14213 = (

let uu____14218 = (

let uu____14219 = (

let uu____14222 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____14222))
in uu____14219.FStar_Syntax_Syntax.n)
in (

let uu____14223 = (

let uu____14224 = (

let uu____14227 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____14227))
in uu____14224.FStar_Syntax_Syntax.n)
in ((uu____14218), (uu____14223))))
in (match (uu____14213) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____14228), uu____14229) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____14236, FStar_Syntax_Syntax.Tm_uinst (uu____14237)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____14244), uu____14245) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____14268, FStar_Syntax_Syntax.Tm_delayed (uu____14269)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____14292), uu____14293) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____14320, FStar_Syntax_Syntax.Tm_ascribed (uu____14321)) -> begin
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

let uu____14354 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____14354))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____14357 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____14357))
end
| (FStar_Syntax_Syntax.Tm_type (uu____14358), FStar_Syntax_Syntax.Tm_type (uu____14359)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____14416 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____14416)) && (

let uu____14424 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____14424)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____14471 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____14471)) && (

let uu____14479 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____14479)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((check "refine bv" (Prims.op_Equality b1.FStar_Syntax_Syntax.index b2.FStar_Syntax_Syntax.index)) && (

let uu____14493 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____14493)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____14548 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____14548)) && (

let uu____14550 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____14550)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____14637 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____14637)) && (

let uu____14639 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____14639)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____14654), uu____14655) -> begin
(

let uu____14656 = (

let uu____14657 = (unlazy t11)
in (term_eq_dbg dbg uu____14657 t21))
in (check "lazy_l" uu____14656))
end
| (uu____14658, FStar_Syntax_Syntax.Tm_lazy (uu____14659)) -> begin
(

let uu____14660 = (

let uu____14661 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____14661))
in (check "lazy_r" uu____14660))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____14697 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____14697))) && (

let uu____14699 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____14699)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____14701), FStar_Syntax_Syntax.Tm_uvar (u2, uu____14703)) -> begin
(check "uvar" (Prims.op_Equality u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((

let uu____14760 = (

let uu____14761 = (eq_quoteinfo qi1 qi2)
in (Prims.op_Equality uu____14761 Equal))
in (check "tm_quoted qi" uu____14760)) && (

let uu____14763 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____14763)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____14790 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____14790)) && (

let uu____14792 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____14792)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____14809 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____14809)) && (

let uu____14811 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____14811))) && (

let uu____14813 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____14813)))
end
| uu____14814 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____14819) -> begin
(fail "unk")
end
| (uu____14820, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____14821), uu____14822) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____14823), uu____14824) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____14825), uu____14826) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____14827), uu____14828) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____14829), uu____14830) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____14831), uu____14832) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____14851), uu____14852) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____14867), uu____14868) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____14875), uu____14876) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____14893), uu____14894) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____14917), uu____14918) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____14931), uu____14932) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____14945), uu____14946) -> begin
(fail "bottom")
end
| (uu____14953, FStar_Syntax_Syntax.Tm_bvar (uu____14954)) -> begin
(fail "bottom")
end
| (uu____14955, FStar_Syntax_Syntax.Tm_name (uu____14956)) -> begin
(fail "bottom")
end
| (uu____14957, FStar_Syntax_Syntax.Tm_fvar (uu____14958)) -> begin
(fail "bottom")
end
| (uu____14959, FStar_Syntax_Syntax.Tm_constant (uu____14960)) -> begin
(fail "bottom")
end
| (uu____14961, FStar_Syntax_Syntax.Tm_type (uu____14962)) -> begin
(fail "bottom")
end
| (uu____14963, FStar_Syntax_Syntax.Tm_abs (uu____14964)) -> begin
(fail "bottom")
end
| (uu____14983, FStar_Syntax_Syntax.Tm_arrow (uu____14984)) -> begin
(fail "bottom")
end
| (uu____14999, FStar_Syntax_Syntax.Tm_refine (uu____15000)) -> begin
(fail "bottom")
end
| (uu____15007, FStar_Syntax_Syntax.Tm_app (uu____15008)) -> begin
(fail "bottom")
end
| (uu____15025, FStar_Syntax_Syntax.Tm_match (uu____15026)) -> begin
(fail "bottom")
end
| (uu____15049, FStar_Syntax_Syntax.Tm_let (uu____15050)) -> begin
(fail "bottom")
end
| (uu____15063, FStar_Syntax_Syntax.Tm_uvar (uu____15064)) -> begin
(fail "bottom")
end
| (uu____15077, FStar_Syntax_Syntax.Tm_meta (uu____15078)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____15111 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____15111))) (fun q1 q2 -> (

let uu____15121 = (

let uu____15122 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____15122 Equal))
in (check "arg qual" uu____15121))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____15145 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____15145))) (fun q1 q2 -> (

let uu____15155 = (

let uu____15156 = (eq_aqual q1 q2)
in (Prims.op_Equality uu____15156 Equal))
in (check "binder qual" uu____15155))) b1 b2))
and lcomp_eq_dbg : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> (fail "lcomp"))
and residual_eq_dbg : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> (fail "residual"))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____15172 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____15172)) && (

let uu____15174 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____15174))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflags  ->  FStar_Syntax_Syntax.cflags  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____15179 uu____15180 -> (match (((uu____15179), (uu____15180))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____15305 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____15305)) && (

let uu____15307 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____15307))) && (

let uu____15309 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____15348 -> begin
false
end)
in (check "branch when" uu____15309)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____15366 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____15366)) && (

let uu____15372 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____15372))) && (

let uu____15374 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____15374))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____15386 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____15386 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____15431) -> begin
(

let uu____15454 = (

let uu____15455 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____15455))
in ((Prims.parse_int "1") + uu____15454))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____15457 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____15457))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____15459 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____15459))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____15466 = (sizeof t1)
in ((FStar_List.length us) + uu____15466))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____15469) -> begin
(

let uu____15494 = (sizeof t1)
in (

let uu____15495 = (FStar_List.fold_left (fun acc uu____15508 -> (match (uu____15508) with
| (bv, uu____15516) -> begin
(

let uu____15521 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____15521))
end)) (Prims.parse_int "0") bs)
in (uu____15494 + uu____15495)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____15548 = (sizeof hd1)
in (

let uu____15549 = (FStar_List.fold_left (fun acc uu____15562 -> (match (uu____15562) with
| (arg, uu____15570) -> begin
(

let uu____15575 = (sizeof arg)
in (acc + uu____15575))
end)) (Prims.parse_int "0") args)
in (uu____15548 + uu____15549)))
end
| uu____15576 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____15587 = (

let uu____15588 = (un_uinst t)
in uu____15588.FStar_Syntax_Syntax.n)
in (match (uu____15587) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____15592 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun t s -> (

let uu____15633 = (FStar_Options.set_options t s)
in (match (uu____15633) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ("Failed to process pragma: use \'fstar --help\' to see which options are available")) r)
end
| FStar_Getopt.Error (s1) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FailToProcessPragma), ((Prims.strcat "Failed to process pragma: " s1))) r)
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
(match ((Prims.op_Equality p FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____15635 -> begin
()
end)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 FStar_Options.Set o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____15641 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____15641 (fun a235 -> ())));
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
((FStar_Options.push ());
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
(FStar_Options.pop ())
end)))


let rec unbound_variables : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun tm -> (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____15672) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____15698) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____15713) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____15714) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____15715) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____15724) -> begin
(

let uu____15749 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____15749) with
| (bs1, t2) -> begin
(

let uu____15758 = (FStar_List.collect (fun uu____15770 -> (match (uu____15770) with
| (b, uu____15780) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____15785 = (unbound_variables t2)
in (FStar_List.append uu____15758 uu____15785)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____15810 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____15810) with
| (bs1, c1) -> begin
(

let uu____15819 = (FStar_List.collect (fun uu____15831 -> (match (uu____15831) with
| (b, uu____15841) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____15846 = (unbound_variables_comp c1)
in (FStar_List.append uu____15819 uu____15846)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____15855 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____15855) with
| (bs, t2) -> begin
(

let uu____15878 = (FStar_List.collect (fun uu____15890 -> (match (uu____15890) with
| (b1, uu____15900) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____15905 = (unbound_variables t2)
in (FStar_List.append uu____15878 uu____15905)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____15934 = (FStar_List.collect (fun uu____15948 -> (match (uu____15948) with
| (x, uu____15960) -> begin
(unbound_variables x)
end)) args)
in (

let uu____15969 = (unbound_variables t1)
in (FStar_List.append uu____15934 uu____15969)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____16010 = (unbound_variables t1)
in (

let uu____16013 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____16028 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____16028) with
| (p, wopt, t2) -> begin
(

let uu____16050 = (unbound_variables t2)
in (

let uu____16053 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____16050 uu____16053)))
end)))))
in (FStar_List.append uu____16010 uu____16013)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____16067) -> begin
(

let uu____16108 = (unbound_variables t1)
in (

let uu____16111 = (

let uu____16114 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____16145 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____16114 uu____16145)))
in (FStar_List.append uu____16108 uu____16111)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____16183 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____16186 = (

let uu____16189 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____16192 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____16197) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____16199 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____16199) with
| (uu____16220, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____16189 uu____16192)))
in (FStar_List.append uu____16183 uu____16186)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____16222, lbs), t1) -> begin
(

let uu____16239 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____16239) with
| (lbs1, t2) -> begin
(

let uu____16254 = (unbound_variables t2)
in (

let uu____16257 = (FStar_List.collect (fun lb -> (

let uu____16264 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____16267 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____16264 uu____16267)))) lbs1)
in (FStar_List.append uu____16254 uu____16257)))
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

let uu____16284 = (unbound_variables t1)
in (

let uu____16287 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____16326 -> (match (uu____16326) with
| (a, uu____16338) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____16347, uu____16348, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____16354, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____16360) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____16367) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____16368) -> begin
[]
end)
in (FStar_List.append uu____16284 uu____16287)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____16375) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____16385) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____16395 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____16398 = (FStar_List.collect (fun uu____16412 -> (match (uu____16412) with
| (a, uu____16424) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____16395 uu____16398)))
end))




