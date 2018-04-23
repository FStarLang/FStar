
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

let uu____91 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id1)::[])))
in (FStar_Ident.set_lid_range uu____91 id1.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (

let uu____97 = (

let uu____100 = (

let uu____103 = (FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (uu____103)::[])
in (FStar_List.append lid.FStar_Ident.ns uu____100))
in (FStar_Ident.lid_of_ids uu____97)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____114 . (FStar_Syntax_Syntax.bv * 'Auu____114)  ->  (FStar_Syntax_Syntax.term * 'Auu____114) = (fun uu____127 -> (match (uu____127) with
| (b, imp) -> begin
(

let uu____134 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____134), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____161 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____161) with
| true -> begin
[]
end
| uu____172 -> begin
(

let uu____173 = (arg_of_non_null_binder b)
in (uu____173)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____199 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____247 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____247) with
| true -> begin
(

let b1 = (

let uu____261 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____261), ((FStar_Pervasives_Native.snd b))))
in (

let uu____262 = (arg_of_non_null_binder b1)
in ((b1), (uu____262))))
end
| uu____275 -> begin
(

let uu____276 = (arg_of_non_null_binder b)
in ((b), (uu____276)))
end)))))
in (FStar_All.pipe_right uu____199 FStar_List.unzip)))


let name_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____372 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____372) with
| true -> begin
(

let uu____377 = b
in (match (uu____377) with
| (a, imp) -> begin
(

let b1 = (

let uu____389 = (

let uu____390 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____390))
in (FStar_Ident.id_of_text uu____389))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____392 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____424 = (

let uu____431 = (

let uu____432 = (

let uu____445 = (name_binders binders)
in ((uu____445), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____432))
in (FStar_Syntax_Syntax.mk uu____431))
in (uu____424 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____463 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____499 -> (match (uu____499) with
| (t, imp) -> begin
(

let uu____510 = (

let uu____511 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____511))
in ((uu____510), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____559 -> (match (uu____559) with
| (t, imp) -> begin
(

let uu____576 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____576), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____588 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____588 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____599 . 'Auu____599  ->  'Auu____599 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____661 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____695 uu____696 -> (match (((uu____695), (uu____696))) with
| ((x, uu____714), (y, uu____716)) -> begin
(

let uu____725 = (

let uu____732 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____732)))
in FStar_Syntax_Syntax.NT (uu____725))
end)) replace_xs with_ys)
end
| uu____737 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____745) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____751, uu____752) -> begin
(unmeta e2)
end
| uu____793 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____806) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____813) -> begin
e1
end
| uu____822 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____824, uu____825) -> begin
(unmeta_safe e2)
end
| uu____866 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____880) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____881) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____891 = (univ_kernel u1)
in (match (uu____891) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____902) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____909) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____919 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____919)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____934), uu____935) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____936, FStar_Syntax_Syntax.U_bvar (uu____937)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____938) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____939, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____940) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____941, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____944), FStar_Syntax_Syntax.U_unif (uu____945)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____954), FStar_Syntax_Syntax.U_name (uu____955)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____982 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____983 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____982 - uu____983)))
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
| uu____1010 -> begin
(

let copt = (

let uu____1014 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____1014 (fun uu____1029 -> (match (uu____1029) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1041 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____1043), uu____1044) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1047, FStar_Syntax_Syntax.U_max (uu____1048)) -> begin
(Prims.parse_int "1")
end
| uu____1051 -> begin
(

let uu____1056 = (univ_kernel u1)
in (match (uu____1056) with
| (k1, n1) -> begin
(

let uu____1063 = (univ_kernel u2)
in (match (uu____1063) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____1071 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____1082 = (compare_univs u1 u2)
in (Prims.op_Equality uu____1082 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (

let uu____1097 = (

let uu____1098 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = uu____1098; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp uu____1097)))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____1115) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____1124) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1146) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1155) -> begin
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

let uu____1181 = (

let uu____1182 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1182))
in {FStar_Syntax_Syntax.comp_univs = uu____1181; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1209 = (

let uu____1210 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1210))
in {FStar_Syntax_Syntax.comp_univs = uu____1209; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let uu___52_1243 = c
in (

let uu____1244 = (

let uu____1245 = (

let uu___53_1246 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___53_1246.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___53_1246.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___53_1246.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___53_1246.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1245))
in {FStar_Syntax_Syntax.n = uu____1244; FStar_Syntax_Syntax.pos = uu___52_1243.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___52_1243.FStar_Syntax_Syntax.vars})))


let lcomp_set_flags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun lc fs -> (

let comp_typ_set_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1267) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____1276) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___54_1287 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___54_1287.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___54_1287.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___54_1287.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___54_1287.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = fs})
in (

let uu___55_1288 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___55_1288.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___55_1288.FStar_Syntax_Syntax.vars}))
end))
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ fs (fun uu____1291 -> (

let uu____1292 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_typ_set_flags uu____1292))))))


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
| uu____1327 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1338) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1347) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___40_1368 -> (match (uu___40_1368) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1369 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___41_1378 -> (match (uu___41_1378) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1379 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___42_1388 -> (match (uu___42_1388) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1389 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___43_1402 -> (match (uu___43_1402) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1403 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___44_1412 -> (match (uu___44_1412) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1413 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1437) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1446) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___45_1459 -> (match (uu___45_1459) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1460 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___46_1488 -> (match (uu___46_1488) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1489 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1500 = (

let uu____1501 = (FStar_Syntax_Subst.compress t)
in uu____1501.FStar_Syntax_Syntax.n)
in (match (uu____1500) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1504, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1522 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1533 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1539 = (

let uu____1540 = (FStar_Syntax_Subst.compress t)
in uu____1540.FStar_Syntax_Syntax.n)
in (match (uu____1539) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1543, c) -> begin
(is_lemma_comp c)
end
| uu____1561 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1628 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1695 = (head_and_args' head1)
in (match (uu____1695) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1752 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1774) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1779 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1785 = (

let uu____1786 = (FStar_Syntax_Subst.compress t)
in uu____1786.FStar_Syntax_Syntax.n)
in (match (uu____1785) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1789, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1811))::uu____1812 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1856 = (head_and_args pats')
in (match (uu____1856) with
| (head1, uu____1872) -> begin
(

let uu____1893 = (

let uu____1894 = (un_uinst head1)
in uu____1894.FStar_Syntax_Syntax.n)
in (match (uu____1893) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1898 -> begin
false
end))
end)))
end
| uu____1899 -> begin
false
end)
end
| uu____1908 -> begin
false
end)
end
| uu____1909 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___47_1923 -> (match (uu___47_1923) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1924 -> begin
false
end)))))
end
| uu____1925 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1940) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1950) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1978) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1987) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___56_1999 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___56_1999.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___56_1999.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___56_1999.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___56_1999.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___48_2012 -> (match (uu___48_2012) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2013 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2033 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2041, uu____2042) -> begin
(unascribe e2)
end
| uu____2083 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2135, uu____2136) -> begin
(ascribe t' k)
end
| uu____2177 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2203 = (

let uu____2212 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2212))
in (uu____2203 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2271 = (

let uu____2272 = (FStar_Syntax_Subst.compress t)
in uu____2272.FStar_Syntax_Syntax.n)
in (match (uu____2271) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2276 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2276))
end
| uu____2277 -> begin
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

let uu____2316 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2316; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.typ = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2324 = (

let uu____2337 = (unascribe t)
in (head_and_args' uu____2337))
in (match (uu____2324) with
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
| uu____2363 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____2369 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____2375 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___49_2451 -> (match (uu___49_2451) with
| true -> begin
Equal
end
| uu____2452 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___50_2458 -> (match (uu___50_2458) with
| true -> begin
Equal
end
| uu____2459 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____2476 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____2488) -> begin
NotEqual
end
| (uu____2489, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____2490) -> begin
Unknown
end
| (uu____2491, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____2537 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2537) with
| true -> begin
(

let uu____2539 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2597 -> (match (uu____2597) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2623 = (eq_tm a1 a2)
in (eq_inj acc uu____2623))
end)) Equal) uu____2539))
end
| uu____2624 -> begin
NotEqual
end)))
in (

let uu____2625 = (

let uu____2630 = (

let uu____2631 = (unmeta t11)
in uu____2631.FStar_Syntax_Syntax.n)
in (

let uu____2634 = (

let uu____2635 = (unmeta t21)
in uu____2635.FStar_Syntax_Syntax.n)
in ((uu____2630), (uu____2634))))
in (match (uu____2625) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____2640), uu____2641) -> begin
(

let uu____2642 = (unlazy t11)
in (eq_tm uu____2642 t21))
end
| (uu____2643, FStar_Syntax_Syntax.Tm_lazy (uu____2644)) -> begin
(

let uu____2645 = (unlazy t21)
in (eq_tm t11 uu____2645))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))) with
| true -> begin
(equal_data f [] g [])
end
| uu____2662 -> begin
(

let uu____2663 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2663))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2676 = (eq_tm f g)
in (eq_and uu____2676 (fun uu____2679 -> (

let uu____2680 = (eq_univs_list us vs)
in (equal_if uu____2680)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2681)), uu____2682) -> begin
Unknown
end
| (uu____2683, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2684))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2687 = (FStar_Const.eq_const c d)
in (equal_iff uu____2687))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1), FStar_Syntax_Syntax.Tm_uvar (u2)) -> begin
(

let uu____2690 = (FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head)
in (equal_if uu____2690))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2735 = (

let uu____2740 = (

let uu____2741 = (un_uinst h1)
in uu____2741.FStar_Syntax_Syntax.n)
in (

let uu____2744 = (

let uu____2745 = (un_uinst h2)
in uu____2745.FStar_Syntax_Syntax.n)
in ((uu____2740), (uu____2744))))
in (match (uu____2735) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((Prims.op_Equality f1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality f2.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
(equal_data f1 args1 f2 args2)
end
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____2757 = (

let uu____2758 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____2758))
in (FStar_List.mem uu____2757 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____2759 -> begin
(

let uu____2764 = (eq_tm h1 h2)
in (eq_and uu____2764 (fun uu____2766 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____2871 = (FStar_List.zip bs1 bs2)
in (

let uu____2934 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____2971 a -> (match (uu____2971) with
| (b1, b2) -> begin
(eq_and a (fun uu____3064 -> (branch_matches b1 b2)))
end)) uu____2871 uu____2934)))
end
| uu____3065 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____3068 = (eq_univs u v1)
in (equal_if uu____3068))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(match ((Prims.op_Equality q1 q2)) with
| true -> begin
(eq_tm t12 t22)
end
| uu____3081 -> begin
Unknown
end)
end
| uu____3082 -> begin
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
| (uu____3165, uu____3166) -> begin
false
end))
in (

let uu____3175 = b1
in (match (uu____3175) with
| (p1, w1, t1) -> begin
(

let uu____3209 = b2
in (match (uu____3209) with
| (p2, w2, t2) -> begin
(

let uu____3243 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____3243) with
| true -> begin
(

let uu____3244 = ((

let uu____3247 = (eq_tm t1 t2)
in (Prims.op_Equality uu____3247 Equal)) && (related_by (fun t11 t21 -> (

let uu____3256 = (eq_tm t11 t21)
in (Prims.op_Equality uu____3256 Equal))) w1 w2))
in (match (uu____3244) with
| true -> begin
Equal
end
| uu____3257 -> begin
Unknown
end))
end
| uu____3258 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____3306))::a11, ((b, uu____3309))::b1) -> begin
(

let uu____3363 = (eq_tm a b)
in (match (uu____3363) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____3364 -> begin
Unknown
end))
end
| uu____3365 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3395) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3401, uu____3402) -> begin
(unrefine t2)
end
| uu____3443 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3449 = (

let uu____3450 = (unrefine t)
in uu____3450.FStar_Syntax_Syntax.n)
in (match (uu____3449) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3455) -> begin
(is_unit t1)
end
| uu____3460 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3466 = (

let uu____3467 = (unrefine t)
in uu____3467.FStar_Syntax_Syntax.n)
in (match (uu____3466) with
| FStar_Syntax_Syntax.Tm_type (uu____3470) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____3473) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3495) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3500, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____3518 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____3524 = (

let uu____3525 = (FStar_Syntax_Subst.compress e)
in uu____3525.FStar_Syntax_Syntax.n)
in (match (uu____3524) with
| FStar_Syntax_Syntax.Tm_abs (uu____3528) -> begin
true
end
| uu____3545 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3551 = (

let uu____3552 = (FStar_Syntax_Subst.compress t)
in uu____3552.FStar_Syntax_Syntax.n)
in (match (uu____3551) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3555) -> begin
true
end
| uu____3568 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3576) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3582, uu____3583) -> begin
(pre_typ t2)
end
| uu____3624 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____3646 = (

let uu____3647 = (un_uinst typ1)
in uu____3647.FStar_Syntax_Syntax.n)
in (match (uu____3646) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____3702 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____3726 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3744, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____3751) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3756, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3767, uu____3768, uu____3769, uu____3770, uu____3771) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3781, uu____3782, uu____3783, uu____3784) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3790, uu____3791, uu____3792, uu____3793, uu____3794) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3800, uu____3801) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____3803, uu____3804) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3807) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____3808) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____3809) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3822 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___51_3845 -> (match (uu___51_3845) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____3858 'Auu____3859 . ('Auu____3858 FStar_Syntax_Syntax.syntax * 'Auu____3859)  ->  FStar_Range.range = (fun uu____3870 -> (match (uu____3870) with
| (hd1, uu____3878) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____3891 'Auu____3892 . ('Auu____3891 FStar_Syntax_Syntax.syntax * 'Auu____3892) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____3983 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____4043 = (FStar_Ident.range_of_lid l)
in (

let uu____4044 = (

let uu____4053 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____4053))
in (uu____4044 FStar_Pervasives_Native.None uu____4043)))
end
| uu____4061 -> begin
(

let e = (

let uu____4073 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____4073 args))
in (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____4088 = (

let uu____4093 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____4093), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4088))
end
| uu____4094 -> begin
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
| uu____4123 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____4144 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____4144) with
| true -> begin
(

let uu____4145 = (

let uu____4150 = (

let uu____4151 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____4151))
in (

let uu____4152 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____4150), (uu____4152))))
in (FStar_Ident.mk_ident uu____4145))
end
| uu____4153 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___57_4155 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___57_4155.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___57_4155.FStar_Syntax_Syntax.sort})
in (

let uu____4156 = (mk_field_projector_name_from_ident lid nm)
in ((uu____4156), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4167) -> begin
ses
end
| uu____4176 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____4185 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____4196 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____4196) with
| FStar_Pervasives_Native.Some (uu____4199) -> begin
(

let uu____4200 = (

let uu____4201 = (

let uu____4202 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____4202))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4201))
in (failwith uu____4200))
end
| uu____4203 -> begin
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
| uu____4278 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____4323 = (

let uu___58_4324 = rc
in (

let uu____4325 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___58_4324.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4325; FStar_Syntax_Syntax.residual_flags = uu___58_4324.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____4323))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____4340 -> begin
(

let body = (

let uu____4342 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____4342))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____4372 = (

let uu____4379 = (

let uu____4380 = (

let uu____4397 = (

let uu____4404 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____4404 bs'))
in (

let uu____4415 = (close_lopt lopt')
in ((uu____4397), (t1), (uu____4415))))
in FStar_Syntax_Syntax.Tm_abs (uu____4380))
in (FStar_Syntax_Syntax.mk uu____4379))
in (uu____4372 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____4431 -> begin
(

let uu____4438 = (

let uu____4445 = (

let uu____4446 = (

let uu____4463 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4470 = (close_lopt lopt)
in ((uu____4463), (body), (uu____4470))))
in FStar_Syntax_Syntax.Tm_abs (uu____4446))
in (FStar_Syntax_Syntax.mk uu____4445))
in (uu____4438 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____4520 -> begin
(

let uu____4527 = (

let uu____4534 = (

let uu____4535 = (

let uu____4548 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4555 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____4548), (uu____4555))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4535))
in (FStar_Syntax_Syntax.mk uu____4534))
in (uu____4527 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____4600 = (

let uu____4601 = (FStar_Syntax_Subst.compress t)
in uu____4601.FStar_Syntax_Syntax.n)
in (match (uu____4600) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____4627) -> begin
(

let uu____4636 = (

let uu____4637 = (FStar_Syntax_Subst.compress tres)
in uu____4637.FStar_Syntax_Syntax.n)
in (match (uu____4636) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____4672 -> begin
t
end))
end
| uu____4673 -> begin
t
end)
end
| uu____4674 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____4687 = (

let uu____4688 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____4688 t.FStar_Syntax_Syntax.pos))
in (

let uu____4689 = (

let uu____4696 = (

let uu____4697 = (

let uu____4704 = (

let uu____4707 = (

let uu____4708 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____4708)::[])
in (FStar_Syntax_Subst.close uu____4707 t))
in ((b), (uu____4704)))
in FStar_Syntax_Syntax.Tm_refine (uu____4697))
in (FStar_Syntax_Syntax.mk uu____4696))
in (uu____4689 FStar_Pervasives_Native.None uu____4687))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4775 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4775) with
| (bs1, c1) -> begin
(

let uu____4792 = (is_total_comp c1)
in (match (uu____4792) with
| true -> begin
(

let uu____4803 = (arrow_formals_comp (comp_result c1))
in (match (uu____4803) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____4848 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____4855; FStar_Syntax_Syntax.index = uu____4856; FStar_Syntax_Syntax.sort = k2}, uu____4858) -> begin
(arrow_formals_comp k2)
end
| uu____4865 -> begin
(

let uu____4866 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4866)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____4894 = (arrow_formals_comp k)
in (match (uu____4894) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____4976 = (

let uu___59_4977 = rc
in (

let uu____4978 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___59_4977.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4978; FStar_Syntax_Syntax.residual_flags = uu___59_4977.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____4976))
end
| uu____4987 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____5019 = (

let uu____5020 = (

let uu____5023 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____5023))
in uu____5020.FStar_Syntax_Syntax.n)
in (match (uu____5019) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____5063 = (aux t2 what)
in (match (uu____5063) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____5123 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____5136 = (aux t FStar_Pervasives_Native.None)
in (match (uu____5136) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____5178 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____5178) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____5335) -> begin
def
end
| (uu____5346, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____5358) -> begin
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

let uu____5452 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____5452) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____5481 -> begin
(

let t' = (arrow binders c)
in (

let uu____5491 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____5491) with
| (uvs1, t'1) -> begin
(

let uu____5510 = (

let uu____5511 = (FStar_Syntax_Subst.compress t'1)
in uu____5511.FStar_Syntax_Syntax.n)
in (match (uu____5510) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____5552 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____5571 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5578 -> begin
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

let uu____5626 = (

let uu____5627 = (pre_typ t)
in uu____5627.FStar_Syntax_Syntax.n)
in (match (uu____5626) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____5631 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____5642 = (

let uu____5643 = (pre_typ t)
in uu____5643.FStar_Syntax_Syntax.n)
in (match (uu____5642) with
| FStar_Syntax_Syntax.Tm_fvar (uu____5646) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____5648) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5670) -> begin
(is_constructed_typ t1 lid)
end
| uu____5675 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____5686) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____5687) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5688) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5690) -> begin
(get_tycon t2)
end
| uu____5711 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5725 = (

let uu____5726 = (un_uinst t)
in uu____5726.FStar_Syntax_Syntax.n)
in (match (uu____5725) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____5730 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____5737 = (

let uu____5740 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____5740))
in (match (uu____5737) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____5753 -> begin
false
end))
end
| uu____5756 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____5769 -> (

let u = (

let uu____5775 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_5 -> FStar_Syntax_Syntax.U_unif (_0_5)) uu____5775))
in (

let uu____5792 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____5792), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____5803 = (eq_tm a a')
in (match (uu____5803) with
| Equal -> begin
true
end
| uu____5804 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____5807 = (

let uu____5814 = (

let uu____5815 = (

let uu____5816 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____5816 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____5815))
in (FStar_Syntax_Syntax.mk uu____5814))
in (uu____5807 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_char : FStar_BaseTypes.char  ->  FStar_Syntax_Syntax.term = (fun c -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.bool_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.not_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.true_lid)


let tac_opaque_attr : FStar_Syntax_Syntax.term = (exp_string "tac_opaque")


let dm4f_bind_range_attr : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.dm4f_bind_range_attr)


let mk_conj_opt : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____5881 = (

let uu____5884 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____5885 = (

let uu____5892 = (

let uu____5893 = (

let uu____5908 = (

let uu____5917 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____5918 = (

let uu____5921 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____5921)::[])
in (uu____5917)::uu____5918))
in ((tand), (uu____5908)))
in FStar_Syntax_Syntax.Tm_app (uu____5893))
in (FStar_Syntax_Syntax.mk uu____5892))
in (uu____5885 FStar_Pervasives_Native.None uu____5884)))
in FStar_Pervasives_Native.Some (uu____5881))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____5962 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____5963 = (

let uu____5970 = (

let uu____5971 = (

let uu____5986 = (

let uu____5995 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____6002 = (

let uu____6011 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____6011)::[])
in (uu____5995)::uu____6002))
in ((op_t), (uu____5986)))
in FStar_Syntax_Syntax.Tm_app (uu____5971))
in (FStar_Syntax_Syntax.mk uu____5970))
in (uu____5963 FStar_Pervasives_Native.None uu____5962))))


let mk_neg : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____6056 = (

let uu____6063 = (

let uu____6064 = (

let uu____6079 = (

let uu____6088 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____6088)::[])
in ((t_not), (uu____6079)))
in FStar_Syntax_Syntax.Tm_app (uu____6064))
in (FStar_Syntax_Syntax.mk uu____6063))
in (uu____6056 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_conj tl1 hd1)
end))


let mk_disj : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_disj tl1 hd1)
end))


let mk_imp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop timp phi1 phi2))


let mk_iff : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e -> (

let uu____6213 = (

let uu____6220 = (

let uu____6221 = (

let uu____6236 = (

let uu____6245 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6245)::[])
in ((b2t_v), (uu____6236)))
in FStar_Syntax_Syntax.Tm_app (uu____6221))
in (FStar_Syntax_Syntax.mk uu____6220))
in (uu____6213 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____6293 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6294 = (

let uu____6301 = (

let uu____6302 = (

let uu____6317 = (

let uu____6326 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6333 = (

let uu____6342 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6342)::[])
in (uu____6326)::uu____6333))
in ((teq), (uu____6317)))
in FStar_Syntax_Syntax.Tm_app (uu____6302))
in (FStar_Syntax_Syntax.mk uu____6301))
in (uu____6294 FStar_Pervasives_Native.None uu____6293))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____6401 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6402 = (

let uu____6409 = (

let uu____6410 = (

let uu____6425 = (

let uu____6434 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6435 = (

let uu____6438 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6439 = (

let uu____6442 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6442)::[])
in (uu____6438)::uu____6439))
in (uu____6434)::uu____6435))
in ((eq_inst), (uu____6425)))
in FStar_Syntax_Syntax.Tm_app (uu____6410))
in (FStar_Syntax_Syntax.mk uu____6409))
in (uu____6402 FStar_Pervasives_Native.None uu____6401)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6479 = (

let uu____6486 = (

let uu____6487 = (

let uu____6502 = (

let uu____6511 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6512 = (

let uu____6515 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____6516 = (

let uu____6519 = (FStar_Syntax_Syntax.as_arg t')
in (uu____6519)::[])
in (uu____6515)::uu____6516))
in (uu____6511)::uu____6512))
in ((t_has_type1), (uu____6502)))
in FStar_Syntax_Syntax.Tm_app (uu____6487))
in (FStar_Syntax_Syntax.mk uu____6486))
in (uu____6479 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6556 = (

let uu____6563 = (

let uu____6564 = (

let uu____6579 = (

let uu____6588 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6589 = (

let uu____6592 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6592)::[])
in (uu____6588)::uu____6589))
in ((t_with_type1), (uu____6579)))
in FStar_Syntax_Syntax.Tm_app (uu____6564))
in (FStar_Syntax_Syntax.mk uu____6563))
in (uu____6556 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____6608 = (

let uu____6615 = (

let uu____6616 = (

let uu____6623 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____6623), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6616))
in (FStar_Syntax_Syntax.mk uu____6615))
in (uu____6608 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____6636 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____6649) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____6660) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____6636) with
| (eff_name, flags1) -> begin
(FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1 (fun uu____6681 -> c0))
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____6759 = (

let uu____6766 = (

let uu____6767 = (

let uu____6782 = (

let uu____6791 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____6798 = (

let uu____6807 = (

let uu____6814 = (

let uu____6815 = (

let uu____6816 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____6816)::[])
in (abs uu____6815 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____6814))
in (uu____6807)::[])
in (uu____6791)::uu____6798))
in ((fa), (uu____6782)))
in FStar_Syntax_Syntax.Tm_app (uu____6767))
in (FStar_Syntax_Syntax.mk uu____6766))
in (uu____6759 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____6905 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____6905) with
| true -> begin
f1
end
| uu____6906 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____6916) -> begin
true
end
| uu____6917 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____6962 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____6962), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____6990 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____6990), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____7003 = (

let uu____7004 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7004))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____7003)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____7078 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____7081 = (

let uu____7090 = (FStar_Syntax_Syntax.as_arg p)
in (uu____7090)::[])
in (mk_app uu____7078 uu____7081)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____7122 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____7125 = (

let uu____7134 = (FStar_Syntax_Syntax.as_arg p)
in (uu____7134)::[])
in (mk_app uu____7122 uu____7125)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let uu____7160 = (head_and_args t)
in (match (uu____7160) with
| (head1, args) -> begin
(

let uu____7199 = (

let uu____7212 = (

let uu____7213 = (un_uinst head1)
in uu____7213.FStar_Syntax_Syntax.n)
in ((uu____7212), (args)))
in (match (uu____7199) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____7228))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____7276 = (

let uu____7281 = (

let uu____7282 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____7282)::[])
in (FStar_Syntax_Subst.open_term uu____7281 p))
in (match (uu____7276) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7321 -> begin
(failwith "impossible")
end)
in (

let uu____7326 = (

let uu____7327 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____7327))
in (match (uu____7326) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7332 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____7333 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____7334 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7360 = (head_and_args t)
in (match (uu____7360) with
| (head1, args) -> begin
(

let uu____7405 = (

let uu____7418 = (

let uu____7419 = (FStar_Syntax_Subst.compress head1)
in uu____7419.FStar_Syntax_Syntax.n)
in ((uu____7418), (args)))
in (match (uu____7405) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7439; FStar_Syntax_Syntax.vars = uu____7440}, (u)::[]), ((t1, uu____7443))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7480 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7512 = (head_and_args t)
in (match (uu____7512) with
| (head1, args) -> begin
(

let uu____7557 = (

let uu____7570 = (

let uu____7571 = (FStar_Syntax_Subst.compress head1)
in uu____7571.FStar_Syntax_Syntax.n)
in ((uu____7570), (args)))
in (match (uu____7557) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7591; FStar_Syntax_Syntax.vars = uu____7592}, (u)::[]), ((t1, uu____7595))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7632 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7656 = (

let uu____7671 = (unmeta t)
in (head_and_args uu____7671))
in (match (uu____7656) with
| (head1, uu____7673) -> begin
(

let uu____7694 = (

let uu____7695 = (un_uinst head1)
in uu____7695.FStar_Syntax_Syntax.n)
in (match (uu____7694) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____7699 -> begin
false
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____7717 = (

let uu____7728 = (

let uu____7729 = (FStar_Syntax_Subst.compress t)
in uu____7729.FStar_Syntax_Syntax.n)
in (match (uu____7728) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____7832 = (

let uu____7841 = (

let uu____7842 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____7842))
in ((b), (uu____7841)))
in FStar_Pervasives_Native.Some (uu____7832))
end
| uu____7855 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____7717 (fun uu____7887 -> (match (uu____7887) with
| (b, c) -> begin
(

let uu____7916 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____7916) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7963 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____7990 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____7990)))


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
| uu____8038 -> begin
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
| uu____8076 -> begin
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
| uu____8112 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____8149)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____8161)) -> begin
(unmeta_monadic t)
end
| uu____8174 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____8258 -> (match (uu____8258) with
| (lid, arity) -> begin
(

let uu____8267 = (

let uu____8282 = (unmeta_monadic f2)
in (head_and_args uu____8282))
in (match (uu____8267) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____8308 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____8308) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____8321 -> begin
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

let uu____8377 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____8377)))
end
| uu____8388 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____8426 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____8443 = (head_and_args t1)
in (match (uu____8443) with
| (t2, args) -> begin
(

let uu____8490 = (un_uinst t2)
in (

let uu____8491 = (FStar_All.pipe_right args (FStar_List.map (fun uu____8524 -> (match (uu____8524) with
| (t3, imp) -> begin
(

let uu____8535 = (unascribe t3)
in ((uu____8535), (imp)))
end))))
in ((uu____8490), (uu____8491))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____8576 = (

let uu____8597 = (flat t1)
in ((qopt), (uu____8597)))
in (match (uu____8576) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8632; FStar_Syntax_Syntax.vars = uu____8633}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8636); FStar_Syntax_Syntax.pos = uu____8637; FStar_Syntax_Syntax.vars = uu____8638}, uu____8639))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8716; FStar_Syntax_Syntax.vars = uu____8717}, (uu____8718)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8721); FStar_Syntax_Syntax.pos = uu____8722; FStar_Syntax_Syntax.vars = uu____8723}, uu____8724))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8812; FStar_Syntax_Syntax.vars = uu____8813}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8816); FStar_Syntax_Syntax.pos = uu____8817; FStar_Syntax_Syntax.vars = uu____8818}, uu____8819))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____8890 = (

let uu____8893 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____8893))
in (aux uu____8890 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8899; FStar_Syntax_Syntax.vars = uu____8900}, (uu____8901)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8904); FStar_Syntax_Syntax.pos = uu____8905; FStar_Syntax_Syntax.vars = uu____8906}, uu____8907))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____8990 = (

let uu____8993 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____8993))
in (aux uu____8990 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____8999) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____9041 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____9041) with
| (bs1, t2) -> begin
(

let uu____9050 = (patterns t2)
in (match (uu____9050) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____9091 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____9092 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____9164 = (un_squash t)
in (FStar_Util.bind_opt uu____9164 (fun t1 -> (

let uu____9174 = (head_and_args' t1)
in (match (uu____9174) with
| (hd1, args) -> begin
(

let uu____9207 = (

let uu____9212 = (

let uu____9213 = (un_uinst hd1)
in uu____9213.FStar_Syntax_Syntax.n)
in ((uu____9212), ((FStar_List.length args))))
in (match (uu____9207) with
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
| uu____9232 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____9261 = (un_squash t)
in (FStar_Util.bind_opt uu____9261 (fun t1 -> (

let uu____9270 = (arrow_one t1)
in (match (uu____9270) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____9285 = (

let uu____9286 = (is_tot_or_gtot_comp c)
in (not (uu____9286)))
in (match (uu____9285) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9289 -> begin
(

let q = (

let uu____9293 = (comp_to_comp_typ_nouniv c)
in uu____9293.FStar_Syntax_Syntax.result_typ)
in (

let uu____9294 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____9294) with
| true -> begin
(

let uu____9297 = (patterns q)
in (match (uu____9297) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____9340 -> begin
(

let uu____9341 = (

let uu____9342 = (

let uu____9347 = (

let uu____9348 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____9349 = (

let uu____9352 = (FStar_Syntax_Syntax.as_arg q)
in (uu____9352)::[])
in (uu____9348)::uu____9349))
in ((FStar_Parser_Const.imp_lid), (uu____9347)))
in BaseConn (uu____9342))
in FStar_Pervasives_Native.Some (uu____9341))
end)))
end))
end
| uu____9353 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____9361 = (un_squash t)
in (FStar_Util.bind_opt uu____9361 (fun t1 -> (

let uu____9386 = (head_and_args' t1)
in (match (uu____9386) with
| (hd1, args) -> begin
(

let uu____9419 = (

let uu____9430 = (

let uu____9431 = (un_uinst hd1)
in uu____9431.FStar_Syntax_Syntax.n)
in ((uu____9430), (args)))
in (match (uu____9419) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____9444))::((a2, uu____9446))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____9465 = (

let uu____9466 = (FStar_Syntax_Subst.compress a2)
in uu____9466.FStar_Syntax_Syntax.n)
in (match (uu____9465) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____9473) -> begin
(

let uu____9500 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____9500) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9539 -> begin
(failwith "impossible")
end)
in (

let uu____9544 = (patterns q1)
in (match (uu____9544) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____9595 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____9596 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____9615 = (destruct_sq_forall phi)
in (match (uu____9615) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____9629 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____9635 = (destruct_sq_exists phi)
in (match (uu____9635) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____9649 -> begin
f1
end))
end
| uu____9652 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____9656 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____9656 (fun uu____9661 -> (

let uu____9662 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____9662 (fun uu____9667 -> (

let uu____9668 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____9668 (fun uu____9673 -> (

let uu____9674 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____9674 (fun uu____9679 -> (

let uu____9680 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____9680 (fun uu____9684 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let unthunk_lemma_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____9692 = (

let uu____9693 = (FStar_Syntax_Subst.compress t)
in uu____9693.FStar_Syntax_Syntax.n)
in (match (uu____9692) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____9700) -> begin
(

let uu____9727 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____9727) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____9753 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____9753) with
| true -> begin
(

let uu____9756 = (

let uu____9765 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____9765)::[])
in (mk_app t uu____9756))
end
| uu____9784 -> begin
e1
end)))
end))
end
| uu____9785 -> begin
(

let uu____9786 = (

let uu____9795 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____9795)::[])
in (mk_app t uu____9786))
end)))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____9830 = (

let uu____9835 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____9835))
in (

let uu____9836 = (

let uu____9837 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____9837))
in (

let uu____9840 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____9830 a.FStar_Syntax_Syntax.action_univs uu____9836 FStar_Parser_Const.effect_Tot_lid uu____9840 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____9863 = (

let uu____9870 = (

let uu____9871 = (

let uu____9886 = (

let uu____9895 = (FStar_Syntax_Syntax.as_arg t)
in (uu____9895)::[])
in ((reify_), (uu____9886)))
in FStar_Syntax_Syntax.Tm_app (uu____9871))
in (FStar_Syntax_Syntax.mk uu____9870))
in (uu____9863 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9915) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____9941 = (unfold_lazy i)
in (delta_qualifier uu____9941))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____9943) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____9944) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____9945) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____9968) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____9969) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____9970) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____9977) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9978) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____9992) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____9997; FStar_Syntax_Syntax.index = uu____9998; FStar_Syntax_Syntax.sort = t2}, uu____10000) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____10008) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____10014, uu____10015) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____10057) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____10078, t2, uu____10080) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____10101, t2) -> begin
(delta_qualifier t2)
end)))


let rec incr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d1) -> begin
(incr_delta_depth d1)
end))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let uu____10131 = (delta_qualifier t)
in (incr_delta_depth uu____10131)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____10137 = (

let uu____10138 = (FStar_Syntax_Subst.compress t)
in uu____10138.FStar_Syntax_Syntax.n)
in (match (uu____10137) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____10141 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____10155 = (

let uu____10170 = (unmeta e)
in (head_and_args uu____10170))
in (match (uu____10155) with
| (head1, args) -> begin
(

let uu____10197 = (

let uu____10208 = (

let uu____10209 = (un_uinst head1)
in uu____10209.FStar_Syntax_Syntax.n)
in ((uu____10208), (args)))
in (match (uu____10197) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____10223) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10239)::((hd1, uu____10241))::((tl1, uu____10243))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____10270 = (

let uu____10273 = (

let uu____10276 = (list_elements tl1)
in (FStar_Util.must uu____10276))
in (hd1)::uu____10273)
in FStar_Pervasives_Native.Some (uu____10270))
end
| uu____10285 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____10305 . ('Auu____10305  ->  'Auu____10305)  ->  'Auu____10305 Prims.list  ->  'Auu____10305 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____10330 = (f a)
in (uu____10330)::[])
end
| (x)::xs -> begin
(

let uu____10335 = (apply_last f xs)
in (x)::uu____10335)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____10381 = (

let uu____10388 = (

let uu____10389 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____10389))
in (FStar_Syntax_Syntax.mk uu____10388))
in (uu____10381 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____10406 = (

let uu____10411 = (

let uu____10412 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10412 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10411 args))
in (uu____10406 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____10428 = (

let uu____10433 = (

let uu____10434 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10434 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10433 args))
in (uu____10428 FStar_Pervasives_Native.None pos)))
in (

let uu____10437 = (

let uu____10438 = (

let uu____10439 = (FStar_Syntax_Syntax.iarg typ)
in (uu____10439)::[])
in (nil uu____10438 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____10467 = (

let uu____10468 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____10475 = (

let uu____10484 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10491 = (

let uu____10500 = (FStar_Syntax_Syntax.as_arg a)
in (uu____10500)::[])
in (uu____10484)::uu____10491))
in (uu____10468)::uu____10475))
in (cons1 uu____10467 t.FStar_Syntax_Syntax.pos))) l uu____10437))))))


let uvar_from_id : Prims.int  ->  (FStar_Syntax_Syntax.binding Prims.list * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id1 uu____10558 -> (match (uu____10558) with
| (gamma, bs, t) -> begin
(

let ctx_u = (

let uu____10601 = (FStar_Syntax_Unionfind.from_id id1)
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____10601; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = bs; FStar_Syntax_Syntax.ctx_uvar_typ = t; FStar_Syntax_Syntax.ctx_uvar_reason = ""; FStar_Syntax_Syntax.ctx_uvar_should_check = true; FStar_Syntax_Syntax.ctx_uvar_range = FStar_Range.dummyRange})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u)) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____10675 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____10782 -> begin
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
| uu____10937 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____10969 -> begin
((

let uu____10971 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____10971) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____10995 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____11159 = (unmeta_safe t1)
in (canon_app uu____11159))
in (

let t21 = (

let uu____11163 = (unmeta_safe t2)
in (canon_app uu____11163))
in (

let uu____11164 = (

let uu____11169 = (

let uu____11170 = (

let uu____11173 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____11173))
in uu____11170.FStar_Syntax_Syntax.n)
in (

let uu____11174 = (

let uu____11175 = (

let uu____11178 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____11178))
in uu____11175.FStar_Syntax_Syntax.n)
in ((uu____11169), (uu____11174))))
in (match (uu____11164) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____11179), uu____11180) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11187, FStar_Syntax_Syntax.Tm_uinst (uu____11188)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____11195), uu____11196) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11221, FStar_Syntax_Syntax.Tm_delayed (uu____11222)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____11247), uu____11248) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11275, FStar_Syntax_Syntax.Tm_ascribed (uu____11276)) -> begin
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

let uu____11309 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____11309))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____11312 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____11312))
end
| (FStar_Syntax_Syntax.Tm_type (uu____11313), FStar_Syntax_Syntax.Tm_type (uu____11314)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____11363 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____11363)) && (

let uu____11369 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____11369)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____11408 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____11408)) && (

let uu____11414 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____11414)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((check "refine bv" (Prims.op_Equality b1.FStar_Syntax_Syntax.index b2.FStar_Syntax_Syntax.index)) && (

let uu____11428 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____11428)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____11475 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____11475)) && (

let uu____11477 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____11477)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____11562 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____11562)) && (

let uu____11564 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____11564)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____11579), uu____11580) -> begin
(

let uu____11581 = (

let uu____11582 = (unlazy t11)
in (term_eq_dbg dbg uu____11582 t21))
in (check "lazy_l" uu____11581))
end
| (uu____11583, FStar_Syntax_Syntax.Tm_lazy (uu____11584)) -> begin
(

let uu____11585 = (

let uu____11586 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____11586))
in (check "lazy_r" uu____11585))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____11622 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____11622))) && (

let uu____11624 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____11624)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1), FStar_Syntax_Syntax.Tm_uvar (u2)) -> begin
(check "uvar" (Prims.op_Equality u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((check "tm_quoted qi" (Prims.op_Equality qi1 qi2)) && (

let uu____11650 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____11650)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____11677 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____11677)) && (

let uu____11679 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____11679)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____11696 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____11696)) && (

let uu____11698 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____11698))) && (

let uu____11700 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____11700)))
end
| uu____11701 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____11706) -> begin
(fail "unk")
end
| (uu____11707, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____11708), uu____11709) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____11710), uu____11711) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____11712), uu____11713) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____11714), uu____11715) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____11716), uu____11717) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____11718), uu____11719) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____11736), uu____11737) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____11750), uu____11751) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____11758), uu____11759) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____11774), uu____11775) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____11798), uu____11799) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____11812), uu____11813) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____11814), uu____11815) -> begin
(fail "bottom")
end
| (uu____11822, FStar_Syntax_Syntax.Tm_bvar (uu____11823)) -> begin
(fail "bottom")
end
| (uu____11824, FStar_Syntax_Syntax.Tm_name (uu____11825)) -> begin
(fail "bottom")
end
| (uu____11826, FStar_Syntax_Syntax.Tm_fvar (uu____11827)) -> begin
(fail "bottom")
end
| (uu____11828, FStar_Syntax_Syntax.Tm_constant (uu____11829)) -> begin
(fail "bottom")
end
| (uu____11830, FStar_Syntax_Syntax.Tm_type (uu____11831)) -> begin
(fail "bottom")
end
| (uu____11832, FStar_Syntax_Syntax.Tm_abs (uu____11833)) -> begin
(fail "bottom")
end
| (uu____11850, FStar_Syntax_Syntax.Tm_arrow (uu____11851)) -> begin
(fail "bottom")
end
| (uu____11864, FStar_Syntax_Syntax.Tm_refine (uu____11865)) -> begin
(fail "bottom")
end
| (uu____11872, FStar_Syntax_Syntax.Tm_app (uu____11873)) -> begin
(fail "bottom")
end
| (uu____11888, FStar_Syntax_Syntax.Tm_match (uu____11889)) -> begin
(fail "bottom")
end
| (uu____11912, FStar_Syntax_Syntax.Tm_let (uu____11913)) -> begin
(fail "bottom")
end
| (uu____11926, FStar_Syntax_Syntax.Tm_uvar (uu____11927)) -> begin
(fail "bottom")
end
| (uu____11928, FStar_Syntax_Syntax.Tm_meta (uu____11929)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____11956 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____11956))) (fun q1 q2 -> (check "arg qual" (Prims.op_Equality q1 q2))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____11977 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____11977))) (fun q1 q2 -> (check "binder qual" (Prims.op_Equality q1 q2))) b1 b2))
and lcomp_eq_dbg : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> (fail "lcomp"))
and residual_eq_dbg : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> (fail "residual"))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____11997 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____11997)) && (

let uu____11999 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____11999))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflags  ->  FStar_Syntax_Syntax.cflags  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____12004 uu____12005 -> (match (((uu____12004), (uu____12005))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____12130 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____12130)) && (

let uu____12132 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____12132))) && (

let uu____12134 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____12149 -> begin
false
end)
in (check "branch when" uu____12134)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____12163 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____12163)) && (

let uu____12169 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____12169))) && (

let uu____12171 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____12171))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____12183 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____12183 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12236) -> begin
(

let uu____12261 = (

let uu____12262 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____12262))
in ((Prims.parse_int "1") + uu____12261))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____12264 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12264))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____12266 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12266))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____12273 = (sizeof t1)
in ((FStar_List.length us) + uu____12273))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12276) -> begin
(

let uu____12297 = (sizeof t1)
in (

let uu____12298 = (FStar_List.fold_left (fun acc uu____12309 -> (match (uu____12309) with
| (bv, uu____12315) -> begin
(

let uu____12316 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____12316))
end)) (Prims.parse_int "0") bs)
in (uu____12297 + uu____12298)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____12339 = (sizeof hd1)
in (

let uu____12340 = (FStar_List.fold_left (fun acc uu____12351 -> (match (uu____12351) with
| (arg, uu____12357) -> begin
(

let uu____12358 = (sizeof arg)
in (acc + uu____12358))
end)) (Prims.parse_int "0") args)
in (uu____12339 + uu____12340)))
end
| uu____12359 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____12370 = (

let uu____12371 = (un_uinst t)
in uu____12371.FStar_Syntax_Syntax.n)
in (match (uu____12370) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____12375 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun t s -> (

let uu____12416 = (FStar_Options.set_options t s)
in (match (uu____12416) with
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
| uu____12418 -> begin
()
end)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 FStar_Options.Set o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____12424 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____12424 (fun a237 -> ())));
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
)
end)))


let rec unbound_variables : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun tm -> (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12450) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____12478) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12481) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____12482) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____12483) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12492) -> begin
(

let uu____12513 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____12513) with
| (bs1, t2) -> begin
(

let uu____12522 = (FStar_List.collect (fun uu____12532 -> (match (uu____12532) with
| (b, uu____12540) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____12541 = (unbound_variables t2)
in (FStar_List.append uu____12522 uu____12541)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____12562 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____12562) with
| (bs1, c1) -> begin
(

let uu____12571 = (FStar_List.collect (fun uu____12581 -> (match (uu____12581) with
| (b, uu____12589) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____12590 = (unbound_variables_comp c1)
in (FStar_List.append uu____12571 uu____12590)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____12599 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____12599) with
| (bs, t2) -> begin
(

let uu____12618 = (FStar_List.collect (fun uu____12628 -> (match (uu____12628) with
| (b1, uu____12636) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____12637 = (unbound_variables t2)
in (FStar_List.append uu____12618 uu____12637)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____12662 = (FStar_List.collect (fun uu____12674 -> (match (uu____12674) with
| (x, uu____12684) -> begin
(unbound_variables x)
end)) args)
in (

let uu____12689 = (unbound_variables t1)
in (FStar_List.append uu____12662 uu____12689)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____12730 = (unbound_variables t1)
in (

let uu____12733 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____12762 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____12762) with
| (p, wopt, t2) -> begin
(

let uu____12784 = (unbound_variables t2)
in (

let uu____12787 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____12784 uu____12787)))
end)))))
in (FStar_List.append uu____12730 uu____12733)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____12801) -> begin
(

let uu____12842 = (unbound_variables t1)
in (

let uu____12845 = (

let uu____12848 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____12879 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____12848 uu____12879)))
in (FStar_List.append uu____12842 uu____12845)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____12917 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____12920 = (

let uu____12923 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____12926 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12931) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____12933 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____12933) with
| (uu____12950, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____12923 uu____12926)))
in (FStar_List.append uu____12917 uu____12920)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____12952, lbs), t1) -> begin
(

let uu____12969 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____12969) with
| (lbs1, t2) -> begin
(

let uu____12984 = (unbound_variables t2)
in (

let uu____12987 = (FStar_List.collect (fun lb -> (

let uu____12994 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____12997 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____12994 uu____12997)))) lbs1)
in (FStar_List.append uu____12984 uu____12987)))
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

let uu____13014 = (unbound_variables t1)
in (

let uu____13017 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____13050 -> (match (uu____13050) with
| (a, uu____13060) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____13065, uu____13066, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____13072, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____13078) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____13085) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____13086) -> begin
[]
end)
in (FStar_List.append uu____13014 uu____13017)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____13093) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____13103) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____13113 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____13116 = (FStar_List.collect (fun uu____13128 -> (match (uu____13128) with
| (a, uu____13138) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____13113 uu____13116)))
end))




