
open Prims
open FStar_Pervasives

let tts_f : (FStar_Syntax_Syntax.term  ->  Prims.string) FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let tts : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let uu____56 = (FStar_ST.op_Bang tts_f)
in (match (uu____56) with
| FStar_Pervasives_Native.None -> begin
"<<hook unset>>"
end
| FStar_Pervasives_Native.Some (f) -> begin
(f t)
end)))


let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id1 -> (

let uu____121 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id1)::[])))
in (FStar_Ident.set_lid_range uu____121 id1.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (

let uu____127 = (

let uu____130 = (

let uu____133 = (FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (uu____133)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____130))
in (FStar_Ident.lid_of_ids uu____127)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____144 . (FStar_Syntax_Syntax.bv * 'Auu____144)  ->  (FStar_Syntax_Syntax.term * 'Auu____144) = (fun uu____157 -> (match (uu____157) with
| (b, imp) -> begin
(

let uu____164 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____164), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____189 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____189) with
| true -> begin
[]
end
| uu____200 -> begin
(

let uu____201 = (arg_of_non_null_binder b)
in (uu____201)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____227 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____273 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____273) with
| true -> begin
(

let b1 = (

let uu____291 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____291), ((FStar_Pervasives_Native.snd b))))
in (

let uu____292 = (arg_of_non_null_binder b1)
in ((b1), (uu____292))))
end
| uu____305 -> begin
(

let uu____306 = (arg_of_non_null_binder b)
in ((b), (uu____306)))
end)))))
in (FStar_All.pipe_right uu____227 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____390 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____390) with
| true -> begin
(

let uu____395 = b
in (match (uu____395) with
| (a, imp) -> begin
(

let b1 = (

let uu____403 = (

let uu____404 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____404))
in (FStar_Ident.id_of_text uu____403))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____406 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____438 = (

let uu____445 = (

let uu____446 = (

let uu____459 = (name_binders binders)
in ((uu____459), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____446))
in (FStar_Syntax_Syntax.mk uu____445))
in (uu____438 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____477 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____519 -> (match (uu____519) with
| (t, imp) -> begin
(

let uu____530 = (

let uu____531 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____531))
in ((uu____530), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____583 -> (match (uu____583) with
| (t, imp) -> begin
(

let uu____600 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____600), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____612 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____612 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____623 . 'Auu____623  ->  'Auu____623 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____685 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____719 uu____720 -> (match (((uu____719), (uu____720))) with
| ((x, uu____738), (y, uu____740)) -> begin
(

let uu____749 = (

let uu____756 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____756)))
in FStar_Syntax_Syntax.NT (uu____749))
end)) replace_xs with_ys)
end
| uu____757 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____765) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____771, uu____772) -> begin
(unmeta e2)
end
| uu____813 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____826) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____833) -> begin
e1
end
| uu____842 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____844, uu____845) -> begin
(unmeta_safe e2)
end
| uu____886 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____900) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____901) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____911 = (univ_kernel u1)
in (match (uu____911) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____922) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____929) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____939 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____939)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____954), uu____955) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____956, FStar_Syntax_Syntax.U_bvar (uu____957)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____958) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____959, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____960) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____961, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____964), FStar_Syntax_Syntax.U_unif (uu____965)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____974), FStar_Syntax_Syntax.U_name (uu____975)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____1002 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____1003 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____1002 - uu____1003)))
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
| uu____1030 -> begin
(

let copt = (

let uu____1034 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____1034 (fun uu____1049 -> (match (uu____1049) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1061 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____1063), uu____1064) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1067, FStar_Syntax_Syntax.U_max (uu____1068)) -> begin
(Prims.parse_int "1")
end
| uu____1071 -> begin
(

let uu____1076 = (univ_kernel u1)
in (match (uu____1076) with
| (k1, n1) -> begin
(

let uu____1083 = (univ_kernel u2)
in (match (uu____1083) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____1091 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____1102 = (compare_univs u1 u2)
in (Prims.op_Equality uu____1102 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (

let uu____1117 = (

let uu____1118 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = uu____1118; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp uu____1117)))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____1135) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____1144) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1166) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1175) -> begin
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

let uu____1201 = (

let uu____1202 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1202))
in {FStar_Syntax_Syntax.comp_univs = uu____1201; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1229 = (

let uu____1230 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1230))
in {FStar_Syntax_Syntax.comp_univs = uu____1229; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let uu___55_1263 = c
in (

let uu____1264 = (

let uu____1265 = (

let uu___56_1266 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___56_1266.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___56_1266.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___56_1266.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___56_1266.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1265))
in {FStar_Syntax_Syntax.n = uu____1264; FStar_Syntax_Syntax.pos = uu___55_1263.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___55_1263.FStar_Syntax_Syntax.vars})))


let lcomp_set_flags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun lc fs -> (

let comp_typ_set_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1287) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____1296) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___57_1307 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___57_1307.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___57_1307.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___57_1307.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___57_1307.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = fs})
in (

let uu___58_1308 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___58_1308.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___58_1308.FStar_Syntax_Syntax.vars}))
end))
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ fs (fun uu____1311 -> (

let uu____1312 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_typ_set_flags uu____1312))))))


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
| uu____1347 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1358) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1367) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___43_1388 -> (match (uu___43_1388) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1389 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___44_1398 -> (match (uu___44_1398) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1399 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___45_1408 -> (match (uu___45_1408) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1409 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___46_1422 -> (match (uu___46_1422) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1423 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___47_1432 -> (match (uu___47_1432) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1433 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1457) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1466) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___48_1479 -> (match (uu___48_1479) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1480 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___49_1508 -> (match (uu___49_1508) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1509 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1520 = (

let uu____1521 = (FStar_Syntax_Subst.compress t)
in uu____1521.FStar_Syntax_Syntax.n)
in (match (uu____1520) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1524, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1542 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1553 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1559 = (

let uu____1560 = (FStar_Syntax_Subst.compress t)
in uu____1560.FStar_Syntax_Syntax.n)
in (match (uu____1559) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1563, c) -> begin
(is_lemma_comp c)
end
| uu____1581 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1648 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1715 = (head_and_args' head1)
in (match (uu____1715) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1772 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1794) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1799 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1805 = (

let uu____1806 = (FStar_Syntax_Subst.compress t)
in uu____1806.FStar_Syntax_Syntax.n)
in (match (uu____1805) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1809, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1831))::uu____1832 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1876 = (head_and_args pats')
in (match (uu____1876) with
| (head1, uu____1892) -> begin
(

let uu____1913 = (

let uu____1914 = (un_uinst head1)
in uu____1914.FStar_Syntax_Syntax.n)
in (match (uu____1913) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1918 -> begin
false
end))
end)))
end
| uu____1919 -> begin
false
end)
end
| uu____1928 -> begin
false
end)
end
| uu____1929 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___50_1943 -> (match (uu___50_1943) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1944 -> begin
false
end)))))
end
| uu____1945 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1960) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1970) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1994) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____2003) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___59_2015 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___59_2015.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___59_2015.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___59_2015.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___59_2015.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___51_2028 -> (match (uu___51_2028) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2029 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2049 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2057, uu____2058) -> begin
(unascribe e2)
end
| uu____2099 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2151, uu____2152) -> begin
(ascribe t' k)
end
| uu____2193 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2219 = (

let uu____2228 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2228))
in (uu____2219 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2293 = (

let uu____2294 = (FStar_Syntax_Subst.compress t)
in uu____2294.FStar_Syntax_Syntax.n)
in (match (uu____2293) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2298 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2298))
end
| uu____2299 -> begin
t
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

let uu____2338 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2338; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.typ = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2346 = (

let uu____2359 = (unascribe t)
in (head_and_args' uu____2359))
in (match (uu____2346) with
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
| uu____2385 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____2391 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____2397 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___52_2473 -> (match (uu___52_2473) with
| true -> begin
Equal
end
| uu____2474 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___53_2480 -> (match (uu___53_2480) with
| true -> begin
Equal
end
| uu____2481 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____2498 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____2510) -> begin
NotEqual
end
| (uu____2511, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____2512) -> begin
Unknown
end
| (uu____2513, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____2559 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2559) with
| true -> begin
(

let uu____2561 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2619 -> (match (uu____2619) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2645 = (eq_tm a1 a2)
in (eq_inj acc uu____2645))
end)) Equal) uu____2561))
end
| uu____2646 -> begin
NotEqual
end)))
in (

let uu____2647 = (

let uu____2652 = (

let uu____2653 = (unmeta t11)
in uu____2653.FStar_Syntax_Syntax.n)
in (

let uu____2656 = (

let uu____2657 = (unmeta t21)
in uu____2657.FStar_Syntax_Syntax.n)
in ((uu____2652), (uu____2656))))
in (match (uu____2647) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____2662), uu____2663) -> begin
(

let uu____2664 = (unlazy t11)
in (eq_tm uu____2664 t21))
end
| (uu____2665, FStar_Syntax_Syntax.Tm_lazy (uu____2666)) -> begin
(

let uu____2667 = (unlazy t21)
in (eq_tm t11 uu____2667))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))) with
| true -> begin
(equal_data f [] g [])
end
| uu____2684 -> begin
(

let uu____2685 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2685))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2698 = (eq_tm f g)
in (eq_and uu____2698 (fun uu____2701 -> (

let uu____2702 = (eq_univs_list us vs)
in (equal_if uu____2702)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2703)), uu____2704) -> begin
Unknown
end
| (uu____2705, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2706))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2709 = (FStar_Const.eq_const c d)
in (equal_iff uu____2709))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____2711), FStar_Syntax_Syntax.Tm_uvar (u2, uu____2713)) -> begin
(

let uu____2762 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (equal_if uu____2762))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2807 = (

let uu____2812 = (

let uu____2813 = (un_uinst h1)
in uu____2813.FStar_Syntax_Syntax.n)
in (

let uu____2816 = (

let uu____2817 = (un_uinst h2)
in uu____2817.FStar_Syntax_Syntax.n)
in ((uu____2812), (uu____2816))))
in (match (uu____2807) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((Prims.op_Equality f1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality f2.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
(equal_data f1 args1 f2 args2)
end
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____2829 = (

let uu____2830 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____2830))
in (FStar_List.mem uu____2829 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____2831 -> begin
(

let uu____2836 = (eq_tm h1 h2)
in (eq_and uu____2836 (fun uu____2838 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____2943 = (FStar_List.zip bs1 bs2)
in (

let uu____3006 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____3043 a -> (match (uu____3043) with
| (b1, b2) -> begin
(eq_and a (fun uu____3136 -> (branch_matches b1 b2)))
end)) uu____2943 uu____3006)))
end
| uu____3137 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____3140 = (eq_univs u v1)
in (equal_if uu____3140))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(match ((Prims.op_Equality q1 q2)) with
| true -> begin
(eq_tm t12 t22)
end
| uu____3153 -> begin
Unknown
end)
end
| uu____3154 -> begin
Unknown
end))))))))))
and branch_matches : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  eq_result = (fun b1 b2 -> (

let related_by = (fun f o1 o2 -> (match (((o1), (o2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(f x y)
end
| (uu____3237, uu____3238) -> begin
false
end))
in (

let uu____3247 = b1
in (match (uu____3247) with
| (p1, w1, t1) -> begin
(

let uu____3281 = b2
in (match (uu____3281) with
| (p2, w2, t2) -> begin
(

let uu____3315 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____3315) with
| true -> begin
(

let uu____3316 = ((

let uu____3319 = (eq_tm t1 t2)
in (Prims.op_Equality uu____3319 Equal)) && (related_by (fun t11 t21 -> (

let uu____3328 = (eq_tm t11 t21)
in (Prims.op_Equality uu____3328 Equal))) w1 w2))
in (match (uu____3316) with
| true -> begin
Equal
end
| uu____3329 -> begin
Unknown
end))
end
| uu____3330 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____3362))::a11, ((b, uu____3365))::b1) -> begin
(

let uu____3419 = (eq_tm a b)
in (match (uu____3419) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____3420 -> begin
Unknown
end))
end
| uu____3421 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3435) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3441, uu____3442) -> begin
(unrefine t2)
end
| uu____3483 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3489 = (

let uu____3490 = (unrefine t)
in uu____3490.FStar_Syntax_Syntax.n)
in (match (uu____3489) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3495) -> begin
(is_unit t1)
end
| uu____3500 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3506 = (

let uu____3507 = (unrefine t)
in uu____3507.FStar_Syntax_Syntax.n)
in (match (uu____3506) with
| FStar_Syntax_Syntax.Tm_type (uu____3510) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.prop_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____3513) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3535) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3540, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____3558 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____3564 = (

let uu____3565 = (FStar_Syntax_Subst.compress e)
in uu____3565.FStar_Syntax_Syntax.n)
in (match (uu____3564) with
| FStar_Syntax_Syntax.Tm_abs (uu____3568) -> begin
true
end
| uu____3585 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3591 = (

let uu____3592 = (FStar_Syntax_Subst.compress t)
in uu____3592.FStar_Syntax_Syntax.n)
in (match (uu____3591) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3595) -> begin
true
end
| uu____3608 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3616) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3622, uu____3623) -> begin
(pre_typ t2)
end
| uu____3664 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____3686 = (

let uu____3687 = (un_uinst typ1)
in uu____3687.FStar_Syntax_Syntax.n)
in (match (uu____3686) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____3742 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____3766 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3784, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____3791) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3796, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3807, uu____3808, uu____3809, uu____3810, uu____3811) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3821, uu____3822, uu____3823, uu____3824) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3830, uu____3831, uu____3832, uu____3833, uu____3834) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3840, uu____3841) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____3843, uu____3844) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3847) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____3848) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____3849) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3862 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___54_3885 -> (match (uu___54_3885) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____3898 'Auu____3899 . ('Auu____3898 FStar_Syntax_Syntax.syntax * 'Auu____3899)  ->  FStar_Range.range = (fun uu____3910 -> (match (uu____3910) with
| (hd1, uu____3918) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____3931 'Auu____3932 . ('Auu____3931 FStar_Syntax_Syntax.syntax * 'Auu____3932) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____4023 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____4079 = (FStar_Ident.range_of_lid l)
in (

let uu____4080 = (

let uu____4087 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____4087))
in (uu____4080 FStar_Pervasives_Native.None uu____4079)))
end
| uu____4091 -> begin
(

let e = (

let uu____4103 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____4103 args))
in (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____4118 = (

let uu____4123 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____4123), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4118))
end
| uu____4124 -> begin
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
| uu____4153 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____4174 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____4174) with
| true -> begin
(

let uu____4175 = (

let uu____4180 = (

let uu____4181 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____4181))
in (

let uu____4182 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____4180), (uu____4182))))
in (FStar_Ident.mk_ident uu____4175))
end
| uu____4183 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___60_4185 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___60_4185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___60_4185.FStar_Syntax_Syntax.sort})
in (

let uu____4186 = (mk_field_projector_name_from_ident lid nm)
in ((uu____4186), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4197) -> begin
ses
end
| uu____4206 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____4215 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____4226 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____4226) with
| FStar_Pervasives_Native.Some (uu____4229) -> begin
(

let uu____4230 = (

let uu____4231 = (

let uu____4232 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____4232))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4231))
in (failwith uu____4230))
end
| uu____4233 -> begin
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
| uu____4308 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____4347 = (

let uu___61_4348 = rc
in (

let uu____4349 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___61_4348.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4349; FStar_Syntax_Syntax.residual_flags = uu___61_4348.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____4347))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____4360 -> begin
(

let body = (

let uu____4362 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____4362))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____4390 = (

let uu____4397 = (

let uu____4398 = (

let uu____4415 = (

let uu____4422 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____4422 bs'))
in (

let uu____4433 = (close_lopt lopt')
in ((uu____4415), (t1), (uu____4433))))
in FStar_Syntax_Syntax.Tm_abs (uu____4398))
in (FStar_Syntax_Syntax.mk uu____4397))
in (uu____4390 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____4449 -> begin
(

let uu____4456 = (

let uu____4463 = (

let uu____4464 = (

let uu____4481 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4482 = (close_lopt lopt)
in ((uu____4481), (body), (uu____4482))))
in FStar_Syntax_Syntax.Tm_abs (uu____4464))
in (FStar_Syntax_Syntax.mk uu____4463))
in (uu____4456 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____4524 -> begin
(

let uu____4531 = (

let uu____4538 = (

let uu____4539 = (

let uu____4552 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4553 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____4552), (uu____4553))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4539))
in (FStar_Syntax_Syntax.mk uu____4538))
in (uu____4531 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____4588 = (

let uu____4589 = (FStar_Syntax_Subst.compress t)
in uu____4589.FStar_Syntax_Syntax.n)
in (match (uu____4588) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____4615) -> begin
(

let uu____4624 = (

let uu____4625 = (FStar_Syntax_Subst.compress tres)
in uu____4625.FStar_Syntax_Syntax.n)
in (match (uu____4624) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____4660 -> begin
t
end))
end
| uu____4661 -> begin
t
end)
end
| uu____4662 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____4675 = (

let uu____4676 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____4676 t.FStar_Syntax_Syntax.pos))
in (

let uu____4677 = (

let uu____4684 = (

let uu____4685 = (

let uu____4692 = (

let uu____4693 = (

let uu____4694 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____4694)::[])
in (FStar_Syntax_Subst.close uu____4693 t))
in ((b), (uu____4692)))
in FStar_Syntax_Syntax.Tm_refine (uu____4685))
in (FStar_Syntax_Syntax.mk uu____4684))
in (uu____4677 FStar_Pervasives_Native.None uu____4675))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4747 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4747) with
| (bs1, c1) -> begin
(

let uu____4764 = (is_total_comp c1)
in (match (uu____4764) with
| true -> begin
(

let uu____4775 = (arrow_formals_comp (comp_result c1))
in (match (uu____4775) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____4820 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____4821; FStar_Syntax_Syntax.index = uu____4822; FStar_Syntax_Syntax.sort = k2}, uu____4824) -> begin
(arrow_formals_comp k2)
end
| uu____4831 -> begin
(

let uu____4832 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4832)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____4860 = (arrow_formals_comp k)
in (match (uu____4860) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____4942 = (

let uu___62_4943 = rc
in (

let uu____4944 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___62_4943.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4944; FStar_Syntax_Syntax.residual_flags = uu___62_4943.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____4942))
end
| uu____4951 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____4983 = (

let uu____4984 = (

let uu____4987 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____4987))
in uu____4984.FStar_Syntax_Syntax.n)
in (match (uu____4983) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____5025 = (aux t2 what)
in (match (uu____5025) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____5085 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____5098 = (aux t FStar_Pervasives_Native.None)
in (match (uu____5098) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____5140 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____5140) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____5301) -> begin
def
end
| (uu____5312, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____5324) -> begin
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


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____5430 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____5430) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____5459 -> begin
(

let t' = (arrow binders c)
in (

let uu____5469 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____5469) with
| (uvs1, t'1) -> begin
(

let uu____5488 = (

let uu____5489 = (FStar_Syntax_Subst.compress t'1)
in uu____5489.FStar_Syntax_Syntax.n)
in (match (uu____5488) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____5530 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____5549 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5556 -> begin
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

let uu____5604 = (

let uu____5605 = (pre_typ t)
in uu____5605.FStar_Syntax_Syntax.n)
in (match (uu____5604) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____5609 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____5620 = (

let uu____5621 = (pre_typ t)
in uu____5621.FStar_Syntax_Syntax.n)
in (match (uu____5620) with
| FStar_Syntax_Syntax.Tm_fvar (uu____5624) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____5626) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5648) -> begin
(is_constructed_typ t1 lid)
end
| uu____5653 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____5664) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____5665) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5666) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5668) -> begin
(get_tycon t2)
end
| uu____5689 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5703 = (

let uu____5704 = (un_uinst t)
in uu____5704.FStar_Syntax_Syntax.n)
in (match (uu____5703) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____5708 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____5715 = (

let uu____5718 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____5718))
in (match (uu____5715) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____5731 -> begin
false
end))
end
| uu____5734 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let kprop : FStar_Syntax_Syntax.term = (

let uu____5739 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.prop_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____5739))


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____5748 -> (

let u = (

let uu____5754 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_5 -> FStar_Syntax_Syntax.U_unif (_0_5)) uu____5754))
in (

let uu____5771 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____5771), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____5786 = (eq_tm a a')
in (match (uu____5786) with
| Equal -> begin
true
end
| uu____5787 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____5790 = (

let uu____5797 = (

let uu____5798 = (

let uu____5799 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____5799 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____5798))
in (FStar_Syntax_Syntax.mk uu____5797))
in (uu____5790 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_char : FStar_BaseTypes.char  ->  FStar_Syntax_Syntax.term = (fun c -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.bool_lid)


let b2p_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.b2p_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.not_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.true_lid)


let tac_opaque_attr : FStar_Syntax_Syntax.term = (exp_string "tac_opaque")


let dm4f_bind_range_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.dm4f_bind_range_attr)


let fail_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.fail_attr)


let mk_conj_opt : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____5858 = (

let uu____5861 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____5862 = (

let uu____5869 = (

let uu____5870 = (

let uu____5885 = (

let uu____5888 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____5889 = (

let uu____5892 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____5892)::[])
in (uu____5888)::uu____5889))
in ((tand), (uu____5885)))
in FStar_Syntax_Syntax.Tm_app (uu____5870))
in (FStar_Syntax_Syntax.mk uu____5869))
in (uu____5862 FStar_Pervasives_Native.None uu____5861)))
in FStar_Pervasives_Native.Some (uu____5858))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____5921 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____5922 = (

let uu____5929 = (

let uu____5930 = (

let uu____5945 = (

let uu____5948 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____5949 = (

let uu____5952 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____5952)::[])
in (uu____5948)::uu____5949))
in ((op_t), (uu____5945)))
in FStar_Syntax_Syntax.Tm_app (uu____5930))
in (FStar_Syntax_Syntax.mk uu____5929))
in (uu____5922 FStar_Pervasives_Native.None uu____5921))))


let mk_neg : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____5967 = (

let uu____5974 = (

let uu____5975 = (

let uu____5990 = (

let uu____5993 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____5993)::[])
in ((t_not), (uu____5990)))
in FStar_Syntax_Syntax.Tm_app (uu____5975))
in (FStar_Syntax_Syntax.mk uu____5974))
in (uu____5967 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_conj tl1 hd1)
end))


let mk_disj : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_disj tl1 hd1)
end))


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop timp phi1 phi2))


let mk_iff : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2p : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e -> (

let uu____6076 = (

let uu____6083 = (

let uu____6084 = (

let uu____6099 = (

let uu____6102 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6102)::[])
in ((b2p_v), (uu____6099)))
in FStar_Syntax_Syntax.Tm_app (uu____6084))
in (FStar_Syntax_Syntax.mk uu____6083))
in (uu____6076 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____6120 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6121 = (

let uu____6128 = (

let uu____6129 = (

let uu____6144 = (

let uu____6147 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6148 = (

let uu____6151 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6151)::[])
in (uu____6147)::uu____6148))
in ((teq), (uu____6144)))
in FStar_Syntax_Syntax.Tm_app (uu____6129))
in (FStar_Syntax_Syntax.mk uu____6128))
in (uu____6121 FStar_Pervasives_Native.None uu____6120))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____6178 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6179 = (

let uu____6186 = (

let uu____6187 = (

let uu____6202 = (

let uu____6205 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6206 = (

let uu____6209 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6210 = (

let uu____6213 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6213)::[])
in (uu____6209)::uu____6210))
in (uu____6205)::uu____6206))
in ((eq_inst), (uu____6202)))
in FStar_Syntax_Syntax.Tm_app (uu____6187))
in (FStar_Syntax_Syntax.mk uu____6186))
in (uu____6179 FStar_Pervasives_Native.None uu____6178)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6242 = (

let uu____6249 = (

let uu____6250 = (

let uu____6265 = (

let uu____6268 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6269 = (

let uu____6272 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____6273 = (

let uu____6276 = (FStar_Syntax_Syntax.as_arg t')
in (uu____6276)::[])
in (uu____6272)::uu____6273))
in (uu____6268)::uu____6269))
in ((t_has_type1), (uu____6265)))
in FStar_Syntax_Syntax.Tm_app (uu____6250))
in (FStar_Syntax_Syntax.mk uu____6249))
in (uu____6242 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6307 = (

let uu____6314 = (

let uu____6315 = (

let uu____6330 = (

let uu____6333 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6334 = (

let uu____6337 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6337)::[])
in (uu____6333)::uu____6334))
in ((t_with_type1), (uu____6330)))
in FStar_Syntax_Syntax.Tm_app (uu____6315))
in (FStar_Syntax_Syntax.mk uu____6314))
in (uu____6307 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____6347 = (

let uu____6354 = (

let uu____6355 = (

let uu____6362 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____6362), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6355))
in (FStar_Syntax_Syntax.mk uu____6354))
in (uu____6347 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____6377 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____6390) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____6401) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____6377) with
| (eff_name, flags1) -> begin
(FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1 (fun uu____6422 -> c0))
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____6496 = (

let uu____6503 = (

let uu____6504 = (

let uu____6519 = (

let uu____6522 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____6523 = (

let uu____6526 = (

let uu____6527 = (

let uu____6528 = (

let uu____6529 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6529)::[])
in (abs uu____6528 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____6527))
in (uu____6526)::[])
in (uu____6522)::uu____6523))
in ((fa), (uu____6519)))
in FStar_Syntax_Syntax.Tm_app (uu____6504))
in (FStar_Syntax_Syntax.mk uu____6503))
in (uu____6496 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____6582 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____6582) with
| true -> begin
f1
end
| uu____6583 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____6593) -> begin
true
end
| uu____6594 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____6639 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____6639), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____6667 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____6667), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____6680 = (

let uu____6681 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____6681))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____6680)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____6755 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____6758 = (

let uu____6767 = (FStar_Syntax_Syntax.as_arg p)
in (uu____6767)::[])
in (mk_app uu____6755 uu____6758)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____6781 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____6784 = (

let uu____6793 = (FStar_Syntax_Syntax.as_arg p)
in (uu____6793)::[])
in (mk_app uu____6781 uu____6784)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____6803 = (head_and_args t)
in (match (uu____6803) with
| (head1, args) -> begin
(

let uu____6844 = (

let uu____6857 = (

let uu____6858 = (un_uinst head1)
in uu____6858.FStar_Syntax_Syntax.n)
in ((uu____6857), (args)))
in (match (uu____6844) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____6875))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____6927 = (

let uu____6932 = (

let uu____6933 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____6933)::[])
in (FStar_Syntax_Subst.open_term uu____6932 p))
in (match (uu____6927) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____6962 -> begin
(failwith "impossible")
end)
in (

let uu____6967 = (

let uu____6968 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____6968))
in (match (uu____6967) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6977 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____6978 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6981 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7009 = (head_and_args t)
in (match (uu____7009) with
| (head1, args) -> begin
(

let uu____7054 = (

let uu____7067 = (

let uu____7068 = (FStar_Syntax_Subst.compress head1)
in uu____7068.FStar_Syntax_Syntax.n)
in ((uu____7067), (args)))
in (match (uu____7054) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7088; FStar_Syntax_Syntax.vars = uu____7089}, (u)::[]), ((t1, uu____7092))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7131 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7163 = (head_and_args t)
in (match (uu____7163) with
| (head1, args) -> begin
(

let uu____7208 = (

let uu____7221 = (

let uu____7222 = (FStar_Syntax_Subst.compress head1)
in uu____7222.FStar_Syntax_Syntax.n)
in ((uu____7221), (args)))
in (match (uu____7208) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7242; FStar_Syntax_Syntax.vars = uu____7243}, (u)::[]), ((t1, uu____7246))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7285 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7309 = (

let uu____7324 = (unmeta t)
in (head_and_args uu____7324))
in (match (uu____7309) with
| (head1, uu____7326) -> begin
(

let uu____7347 = (

let uu____7348 = (un_uinst head1)
in uu____7348.FStar_Syntax_Syntax.n)
in (match (uu____7347) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2p_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____7352 -> begin
false
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____7370 = (

let uu____7383 = (

let uu____7384 = (FStar_Syntax_Subst.compress t)
in uu____7384.FStar_Syntax_Syntax.n)
in (match (uu____7383) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____7493 = (

let uu____7502 = (

let uu____7503 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____7503))
in ((b), (uu____7502)))
in FStar_Pervasives_Native.Some (uu____7493))
end
| uu____7516 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____7370 (fun uu____7552 -> (match (uu____7552) with
| (b, c) -> begin
(

let uu____7587 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____7587) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7634 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____7661 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____7661)))


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
| uu____7709 -> begin
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
| uu____7747 -> begin
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
| uu____7783 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____7820)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____7832)) -> begin
(unmeta_monadic t)
end
| uu____7845 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____7929 -> (match (uu____7929) with
| (lid, arity) -> begin
(

let uu____7938 = (

let uu____7953 = (unmeta_monadic f2)
in (head_and_args uu____7953))
in (match (uu____7938) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____7979 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____7979) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____8000 -> begin
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

let uu____8056 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____8056)))
end
| uu____8067 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____8105 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____8122 = (head_and_args t1)
in (match (uu____8122) with
| (t2, args) -> begin
(

let uu____8169 = (un_uinst t2)
in (

let uu____8170 = (FStar_All.pipe_right args (FStar_List.map (fun uu____8203 -> (match (uu____8203) with
| (t3, imp) -> begin
(

let uu____8214 = (unascribe t3)
in ((uu____8214), (imp)))
end))))
in ((uu____8169), (uu____8170))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____8255 = (

let uu____8272 = (flat t1)
in ((qopt), (uu____8272)))
in (match (uu____8255) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8299; FStar_Syntax_Syntax.vars = uu____8300}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8303); FStar_Syntax_Syntax.pos = uu____8304; FStar_Syntax_Syntax.vars = uu____8305}, uu____8306))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8383; FStar_Syntax_Syntax.vars = uu____8384}, (uu____8385)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8388); FStar_Syntax_Syntax.pos = uu____8389; FStar_Syntax_Syntax.vars = uu____8390}, uu____8391))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8479; FStar_Syntax_Syntax.vars = uu____8480}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8483); FStar_Syntax_Syntax.pos = uu____8484; FStar_Syntax_Syntax.vars = uu____8485}, uu____8486))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____8557 = (

let uu____8560 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____8560))
in (aux uu____8557 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8566; FStar_Syntax_Syntax.vars = uu____8567}, (uu____8568)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8571); FStar_Syntax_Syntax.pos = uu____8572; FStar_Syntax_Syntax.vars = uu____8573}, uu____8574))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____8657 = (

let uu____8660 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____8660))
in (aux uu____8657 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____8666) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____8700 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____8700) with
| (bs1, t2) -> begin
(

let uu____8709 = (patterns t2)
in (match (uu____8709) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____8760 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____8771 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____8839 = (un_squash t)
in (FStar_Util.bind_opt uu____8839 (fun t1 -> (

let uu____8855 = (head_and_args' t1)
in (match (uu____8855) with
| (hd1, args) -> begin
(

let uu____8888 = (

let uu____8893 = (

let uu____8894 = (un_uinst hd1)
in uu____8894.FStar_Syntax_Syntax.n)
in ((uu____8893), ((FStar_List.length args))))
in (match (uu____8888) with
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
| uu____8977 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____9006 = (un_squash t)
in (FStar_Util.bind_opt uu____9006 (fun t1 -> (

let uu____9021 = (arrow_one t1)
in (match (uu____9021) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____9036 = (

let uu____9037 = (is_tot_or_gtot_comp c)
in (not (uu____9037)))
in (match (uu____9036) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9040 -> begin
(

let q = (

let uu____9044 = (comp_to_comp_typ_nouniv c)
in uu____9044.FStar_Syntax_Syntax.result_typ)
in (

let uu____9045 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____9045) with
| true -> begin
(

let uu____9048 = (patterns q)
in (match (uu____9048) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____9103 -> begin
(

let uu____9104 = (

let uu____9105 = (

let uu____9110 = (

let uu____9113 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____9114 = (

let uu____9117 = (FStar_Syntax_Syntax.as_arg q)
in (uu____9117)::[])
in (uu____9113)::uu____9114))
in ((FStar_Parser_Const.imp_lid), (uu____9110)))
in BaseConn (uu____9105))
in FStar_Pervasives_Native.Some (uu____9104))
end)))
end))
end
| uu____9120 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____9128 = (un_squash t)
in (FStar_Util.bind_opt uu____9128 (fun t1 -> (

let uu____9159 = (head_and_args' t1)
in (match (uu____9159) with
| (hd1, args) -> begin
(

let uu____9192 = (

let uu____9205 = (

let uu____9206 = (un_uinst hd1)
in uu____9206.FStar_Syntax_Syntax.n)
in ((uu____9205), (args)))
in (match (uu____9192) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____9221))::((a2, uu____9223))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____9258 = (

let uu____9259 = (FStar_Syntax_Subst.compress a2)
in uu____9259.FStar_Syntax_Syntax.n)
in (match (uu____9258) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____9266) -> begin
(

let uu____9293 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____9293) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9332 -> begin
(failwith "impossible")
end)
in (

let uu____9337 = (patterns q1)
in (match (uu____9337) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____9404 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____9405 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____9426 = (destruct_sq_forall phi)
in (match (uu____9426) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____9448 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____9454 = (destruct_sq_exists phi)
in (match (uu____9454) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____9476 -> begin
f1
end))
end
| uu____9479 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____9483 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____9483 (fun uu____9488 -> (

let uu____9489 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____9489 (fun uu____9494 -> (

let uu____9495 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____9495 (fun uu____9500 -> (

let uu____9501 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____9501 (fun uu____9506 -> (

let uu____9507 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____9507 (fun uu____9511 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let unthunk_lemma_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____9519 = (

let uu____9520 = (FStar_Syntax_Subst.compress t)
in uu____9520.FStar_Syntax_Syntax.n)
in (match (uu____9519) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____9527) -> begin
(

let uu____9554 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____9554) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____9580 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____9580) with
| true -> begin
(

let uu____9583 = (

let uu____9592 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____9592)::[])
in (mk_app t uu____9583))
end
| uu____9593 -> begin
e1
end)))
end))
end
| uu____9594 -> begin
(

let uu____9595 = (

let uu____9604 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____9604)::[])
in (mk_app t uu____9595))
end)))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____9621 = (

let uu____9626 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____9626))
in (

let uu____9627 = (

let uu____9628 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____9628))
in (

let uu____9631 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____9621 a.FStar_Syntax_Syntax.action_univs uu____9627 FStar_Parser_Const.effect_Tot_lid uu____9631 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____9660 = (

let uu____9667 = (

let uu____9668 = (

let uu____9683 = (

let uu____9686 = (FStar_Syntax_Syntax.as_arg t)
in (uu____9686)::[])
in ((reify_), (uu____9683)))
in FStar_Syntax_Syntax.Tm_app (uu____9668))
in (FStar_Syntax_Syntax.mk uu____9667))
in (uu____9660 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9700) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____9726 = (unfold_lazy i)
in (delta_qualifier uu____9726))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____9728) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____9729) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____9730) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9753) -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____9770) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____9771) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____9778) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9779) -> begin
FStar_Syntax_Syntax.delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____9793) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____9798; FStar_Syntax_Syntax.index = uu____9799; FStar_Syntax_Syntax.sort = t2}, uu____9801) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____9809) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____9815, uu____9816) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____9858) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____9879, t2, uu____9881) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____9902, t2) -> begin
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

let uu____9933 = (delta_qualifier t)
in (incr_delta_depth uu____9933)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9939 = (

let uu____9940 = (FStar_Syntax_Subst.compress t)
in uu____9940.FStar_Syntax_Syntax.n)
in (match (uu____9939) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____9943 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____9957 = (

let uu____9972 = (unmeta e)
in (head_and_args uu____9972))
in (match (uu____9957) with
| (head1, args) -> begin
(

let uu____9999 = (

let uu____10012 = (

let uu____10013 = (un_uinst head1)
in uu____10013.FStar_Syntax_Syntax.n)
in ((uu____10012), (args)))
in (match (uu____9999) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____10029) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10049)::((hd1, uu____10051))::((tl1, uu____10053))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____10100 = (

let uu____10105 = (

let uu____10110 = (list_elements tl1)
in (FStar_Util.must uu____10110))
in (hd1)::uu____10105)
in FStar_Pervasives_Native.Some (uu____10100))
end
| uu____10123 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____10144 . ('Auu____10144  ->  'Auu____10144)  ->  'Auu____10144 Prims.list  ->  'Auu____10144 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____10169 = (f a)
in (uu____10169)::[])
end
| (x)::xs -> begin
(

let uu____10174 = (apply_last f xs)
in (x)::uu____10174)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____10220 = (

let uu____10227 = (

let uu____10228 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____10228))
in (FStar_Syntax_Syntax.mk uu____10227))
in (uu____10220 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____10245 = (

let uu____10250 = (

let uu____10251 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10251 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10250 args))
in (uu____10245 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____10267 = (

let uu____10272 = (

let uu____10273 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10273 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10272 args))
in (uu____10267 FStar_Pervasives_Native.None pos)))
in (

let uu____10276 = (

let uu____10277 = (

let uu____10278 = (FStar_Syntax_Syntax.iarg typ)
in (uu____10278)::[])
in (nil uu____10277 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____10284 = (

let uu____10285 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____10286 = (

let uu____10289 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10290 = (

let uu____10293 = (FStar_Syntax_Syntax.as_arg a)
in (uu____10293)::[])
in (uu____10289)::uu____10290))
in (uu____10285)::uu____10286))
in (cons1 uu____10284 t.FStar_Syntax_Syntax.pos))) l uu____10276))))))


let uvar_from_id : Prims.int  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id1 t -> (

let uu____10306 = (

let uu____10313 = (

let uu____10314 = (

let uu____10331 = (FStar_Syntax_Unionfind.from_id id1)
in ((uu____10331), (t)))
in FStar_Syntax_Syntax.Tm_uvar (uu____10314))
in (FStar_Syntax_Syntax.mk uu____10313))
in (uu____10306 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____10398 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____10505 -> begin
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
| uu____10660 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____10716 -> begin
((

let uu____10718 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____10718) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____10748 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____10912 = (unmeta_safe t1)
in (canon_app uu____10912))
in (

let t21 = (

let uu____10916 = (unmeta_safe t2)
in (canon_app uu____10916))
in (

let uu____10917 = (

let uu____10922 = (

let uu____10923 = (

let uu____10926 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____10926))
in uu____10923.FStar_Syntax_Syntax.n)
in (

let uu____10927 = (

let uu____10928 = (

let uu____10931 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____10931))
in uu____10928.FStar_Syntax_Syntax.n)
in ((uu____10922), (uu____10927))))
in (match (uu____10917) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____10932), uu____10933) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____10940, FStar_Syntax_Syntax.Tm_uinst (uu____10941)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____10948), uu____10949) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____10974, FStar_Syntax_Syntax.Tm_delayed (uu____10975)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____11000), uu____11001) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11028, FStar_Syntax_Syntax.Tm_ascribed (uu____11029)) -> begin
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

let uu____11062 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____11062))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____11065 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____11065))
end
| (FStar_Syntax_Syntax.Tm_type (uu____11066), FStar_Syntax_Syntax.Tm_type (uu____11067)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____11116 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____11116)) && (

let uu____11122 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____11122)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____11161 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____11161)) && (

let uu____11167 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____11167)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((check "refine bv" (Prims.op_Equality b1.FStar_Syntax_Syntax.index b2.FStar_Syntax_Syntax.index)) && (

let uu____11181 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____11181)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____11228 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____11228)) && (

let uu____11230 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____11230)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____11315 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____11315)) && (

let uu____11317 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____11317)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____11332), uu____11333) -> begin
(

let uu____11334 = (

let uu____11335 = (unlazy t11)
in (term_eq_dbg dbg uu____11335 t21))
in (check "lazy_l" uu____11334))
end
| (uu____11336, FStar_Syntax_Syntax.Tm_lazy (uu____11337)) -> begin
(

let uu____11338 = (

let uu____11339 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____11339))
in (check "lazy_r" uu____11338))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____11375 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____11375))) && (

let uu____11377 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____11377)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____11379), FStar_Syntax_Syntax.Tm_uvar (u2, uu____11381)) -> begin
(check "uvar" (Prims.op_Equality u1 u2))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((check "tm_quoted qi" (Prims.op_Equality qi1 qi2)) && (

let uu____11453 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____11453)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____11480 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____11480)) && (

let uu____11482 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____11482)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____11499 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____11499)) && (

let uu____11501 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____11501))) && (

let uu____11503 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____11503)))
end
| uu____11504 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____11509) -> begin
(fail "unk")
end
| (uu____11510, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____11511), uu____11512) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____11513), uu____11514) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____11515), uu____11516) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____11517), uu____11518) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____11519), uu____11520) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____11521), uu____11522) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____11539), uu____11540) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11553), uu____11554) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____11561), uu____11562) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____11577), uu____11578) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____11601), uu____11602) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11615), uu____11616) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____11633), uu____11634) -> begin
(fail "bottom")
end
| (uu____11641, FStar_Syntax_Syntax.Tm_bvar (uu____11642)) -> begin
(fail "bottom")
end
| (uu____11643, FStar_Syntax_Syntax.Tm_name (uu____11644)) -> begin
(fail "bottom")
end
| (uu____11645, FStar_Syntax_Syntax.Tm_fvar (uu____11646)) -> begin
(fail "bottom")
end
| (uu____11647, FStar_Syntax_Syntax.Tm_constant (uu____11648)) -> begin
(fail "bottom")
end
| (uu____11649, FStar_Syntax_Syntax.Tm_type (uu____11650)) -> begin
(fail "bottom")
end
| (uu____11651, FStar_Syntax_Syntax.Tm_abs (uu____11652)) -> begin
(fail "bottom")
end
| (uu____11669, FStar_Syntax_Syntax.Tm_arrow (uu____11670)) -> begin
(fail "bottom")
end
| (uu____11683, FStar_Syntax_Syntax.Tm_refine (uu____11684)) -> begin
(fail "bottom")
end
| (uu____11691, FStar_Syntax_Syntax.Tm_app (uu____11692)) -> begin
(fail "bottom")
end
| (uu____11707, FStar_Syntax_Syntax.Tm_match (uu____11708)) -> begin
(fail "bottom")
end
| (uu____11731, FStar_Syntax_Syntax.Tm_let (uu____11732)) -> begin
(fail "bottom")
end
| (uu____11745, FStar_Syntax_Syntax.Tm_uvar (uu____11746)) -> begin
(fail "bottom")
end
| (uu____11763, FStar_Syntax_Syntax.Tm_meta (uu____11764)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____11791 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____11791))) (fun q1 q2 -> (check "arg qual" (Prims.op_Equality q1 q2))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____11812 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____11812))) (fun q1 q2 -> (check "binder qual" (Prims.op_Equality q1 q2))) b1 b2))
and lcomp_eq_dbg : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> (fail "lcomp"))
and residual_eq_dbg : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> (fail "residual"))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____11832 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____11832)) && (

let uu____11834 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____11834))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflags  ->  FStar_Syntax_Syntax.cflags  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____11839 uu____11840 -> (match (((uu____11839), (uu____11840))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____11965 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____11965)) && (

let uu____11967 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____11967))) && (

let uu____11969 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____12008 -> begin
false
end)
in (check "branch when" uu____11969)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____12026 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____12026)) && (

let uu____12032 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____12032))) && (

let uu____12034 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____12034))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____12046 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____12046 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12111) -> begin
(

let uu____12136 = (

let uu____12137 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____12137))
in ((Prims.parse_int "1") + uu____12136))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____12139 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12139))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____12141 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12141))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____12148 = (sizeof t1)
in ((FStar_List.length us) + uu____12148))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12151) -> begin
(

let uu____12172 = (sizeof t1)
in (

let uu____12173 = (FStar_List.fold_left (fun acc uu____12184 -> (match (uu____12184) with
| (bv, uu____12190) -> begin
(

let uu____12191 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____12191))
end)) (Prims.parse_int "0") bs)
in (uu____12172 + uu____12173)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____12214 = (sizeof hd1)
in (

let uu____12215 = (FStar_List.fold_left (fun acc uu____12226 -> (match (uu____12226) with
| (arg, uu____12232) -> begin
(

let uu____12233 = (sizeof arg)
in (acc + uu____12233))
end)) (Prims.parse_int "0") args)
in (uu____12214 + uu____12215)))
end
| uu____12234 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____12245 = (

let uu____12246 = (un_uinst t)
in uu____12246.FStar_Syntax_Syntax.n)
in (match (uu____12245) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____12250 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun t s -> (

let uu____12291 = (FStar_Options.set_options t s)
in (match (uu____12291) with
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
| uu____12293 -> begin
()
end)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 FStar_Options.Set o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____12299 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____12299 (fun a238 -> ())));
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
)
end)))


let rec unbound_variables : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv Prims.list = (fun tm -> (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12319) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (x, t1) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12375) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____12376) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____12377) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12386) -> begin
(

let uu____12407 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____12407) with
| (bs1, t2) -> begin
(

let uu____12416 = (FStar_List.collect (fun uu____12426 -> (match (uu____12426) with
| (b, uu____12434) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____12435 = (unbound_variables t2)
in (FStar_List.append uu____12416 uu____12435)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____12456 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12456) with
| (bs1, c1) -> begin
(

let uu____12465 = (FStar_List.collect (fun uu____12475 -> (match (uu____12475) with
| (b, uu____12483) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____12484 = (unbound_variables_comp c1)
in (FStar_List.append uu____12465 uu____12484)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____12493 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____12493) with
| (bs, t2) -> begin
(

let uu____12516 = (FStar_List.collect (fun uu____12526 -> (match (uu____12526) with
| (b1, uu____12534) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____12535 = (unbound_variables t2)
in (FStar_List.append uu____12516 uu____12535)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____12560 = (FStar_List.collect (fun uu____12570 -> (match (uu____12570) with
| (x, uu____12578) -> begin
(unbound_variables x)
end)) args)
in (

let uu____12579 = (unbound_variables t1)
in (FStar_List.append uu____12560 uu____12579)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____12620 = (unbound_variables t1)
in (

let uu____12623 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____12652 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____12652) with
| (p, wopt, t2) -> begin
(

let uu____12674 = (unbound_variables t2)
in (

let uu____12677 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____12674 uu____12677)))
end)))))
in (FStar_List.append uu____12620 uu____12623)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____12691) -> begin
(

let uu____12732 = (unbound_variables t1)
in (

let uu____12735 = (

let uu____12738 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____12769 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____12738 uu____12769)))
in (FStar_List.append uu____12732 uu____12735)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____12807 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____12810 = (

let uu____12813 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____12816 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12821) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____12823 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____12823) with
| (uu____12844, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____12813 uu____12816)))
in (FStar_List.append uu____12807 uu____12810)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____12846, lbs), t1) -> begin
(

let uu____12863 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____12863) with
| (lbs1, t2) -> begin
(

let uu____12878 = (unbound_variables t2)
in (

let uu____12881 = (FStar_List.collect (fun lb -> (

let uu____12888 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____12891 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____12888 uu____12891)))) lbs1)
in (FStar_List.append uu____12878 uu____12881)))
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

let uu____12908 = (unbound_variables t1)
in (

let uu____12911 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____12940 -> (match (uu____12940) with
| (a, uu____12948) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____12949, uu____12950, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____12956, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____12962) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____12969) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____12970) -> begin
[]
end)
in (FStar_List.append uu____12908 uu____12911)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____12975) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____12985) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____12995 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____12998 = (FStar_List.collect (fun uu____13008 -> (match (uu____13008) with
| (a, uu____13016) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____12995 uu____12998)))
end))




