
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

let uu____173 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____173) with
| true -> begin
[]
end
| uu____184 -> begin
(

let uu____185 = (arg_of_non_null_binder b)
in (uu____185)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____211 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____275 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____275) with
| true -> begin
(

let b1 = (

let uu____293 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____293), ((FStar_Pervasives_Native.snd b))))
in (

let uu____294 = (arg_of_non_null_binder b1)
in ((b1), (uu____294))))
end
| uu____307 -> begin
(

let uu____308 = (arg_of_non_null_binder b)
in ((b), (uu____308)))
end)))))
in (FStar_All.pipe_right uu____211 FStar_List.unzip)))


let name_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____408 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____408) with
| true -> begin
(

let uu____413 = b
in (match (uu____413) with
| (a, imp) -> begin
(

let b1 = (

let uu____425 = (

let uu____426 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____426))
in (FStar_Ident.id_of_text uu____425))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____428 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____460 = (

let uu____467 = (

let uu____468 = (

let uu____481 = (name_binders binders)
in ((uu____481), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____468))
in (FStar_Syntax_Syntax.mk uu____467))
in (uu____460 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____499 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____535 -> (match (uu____535) with
| (t, imp) -> begin
(

let uu____546 = (

let uu____547 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____547))
in ((uu____546), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____595 -> (match (uu____595) with
| (t, imp) -> begin
(

let uu____612 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____612), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____624 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____624 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____635 . 'Auu____635  ->  'Auu____635 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____697 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____731 uu____732 -> (match (((uu____731), (uu____732))) with
| ((x, uu____750), (y, uu____752)) -> begin
(

let uu____761 = (

let uu____768 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____768)))
in FStar_Syntax_Syntax.NT (uu____761))
end)) replace_xs with_ys)
end
| uu____773 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____781) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____787, uu____788) -> begin
(unmeta e2)
end
| uu____829 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____842) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____849) -> begin
e1
end
| uu____858 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____860, uu____861) -> begin
(unmeta_safe e2)
end
| uu____902 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____916) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____917) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____927 = (univ_kernel u1)
in (match (uu____927) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____938) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____945) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____955 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____955)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____970), uu____971) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____972, FStar_Syntax_Syntax.U_bvar (uu____973)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____974) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____975, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____976) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____977, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____980), FStar_Syntax_Syntax.U_unif (uu____981)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____990), FStar_Syntax_Syntax.U_name (uu____991)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____1018 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____1019 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____1018 - uu____1019)))
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
| uu____1046 -> begin
(

let copt = (

let uu____1050 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____1050 (fun uu____1065 -> (match (uu____1065) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1077 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____1079), uu____1080) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____1083, FStar_Syntax_Syntax.U_max (uu____1084)) -> begin
(Prims.parse_int "1")
end
| uu____1087 -> begin
(

let uu____1092 = (univ_kernel u1)
in (match (uu____1092) with
| (k1, n1) -> begin
(

let uu____1099 = (univ_kernel u2)
in (match (uu____1099) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____1107 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____1118 = (compare_univs u1 u2)
in (Prims.op_Equality uu____1118 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (

let uu____1133 = (

let uu____1134 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = uu____1134; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp uu____1133)))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____1151) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____1160) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1182) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1191) -> begin
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

let uu____1217 = (

let uu____1218 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1218))
in {FStar_Syntax_Syntax.comp_univs = uu____1217; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1245 = (

let uu____1246 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1246))
in {FStar_Syntax_Syntax.comp_univs = uu____1245; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let uu___52_1279 = c
in (

let uu____1280 = (

let uu____1281 = (

let uu___53_1282 = (comp_to_comp_typ_nouniv c)
in {FStar_Syntax_Syntax.comp_univs = uu___53_1282.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___53_1282.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___53_1282.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___53_1282.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1281))
in {FStar_Syntax_Syntax.n = uu____1280; FStar_Syntax_Syntax.pos = uu___52_1279.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___52_1279.FStar_Syntax_Syntax.vars})))


let lcomp_set_flags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun lc fs -> (

let comp_typ_set_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1307) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (uu____1316) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___54_1327 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___54_1327.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___54_1327.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___54_1327.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___54_1327.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = fs})
in (

let uu___55_1328 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___55_1328.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___55_1328.FStar_Syntax_Syntax.vars}))
end))
in (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ fs (fun uu____1331 -> (

let uu____1332 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_typ_set_flags uu____1332))))))


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
| uu____1367 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1378) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1387) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___40_1408 -> (match (uu___40_1408) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1409 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___41_1418 -> (match (uu___41_1418) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1419 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___42_1428 -> (match (uu___42_1428) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1429 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___43_1442 -> (match (uu___43_1442) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1443 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___44_1452 -> (match (uu___44_1452) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1453 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1477) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1486) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___45_1499 -> (match (uu___45_1499) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1500 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_div_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___46_1528 -> (match (uu___46_1528) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1529 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1540 = (

let uu____1541 = (FStar_Syntax_Subst.compress t)
in uu____1541.FStar_Syntax_Syntax.n)
in (match (uu____1540) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1544, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1562 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1573 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1579 = (

let uu____1580 = (FStar_Syntax_Subst.compress t)
in uu____1580.FStar_Syntax_Syntax.n)
in (match (uu____1579) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1583, c) -> begin
(is_lemma_comp c)
end
| uu____1601 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1668 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1735 = (head_and_args' head1)
in (match (uu____1735) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1792 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1814) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1819 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1825 = (

let uu____1826 = (FStar_Syntax_Subst.compress t)
in uu____1826.FStar_Syntax_Syntax.n)
in (match (uu____1825) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1829, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1851))::uu____1852 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1896 = (head_and_args pats')
in (match (uu____1896) with
| (head1, uu____1912) -> begin
(

let uu____1933 = (

let uu____1934 = (un_uinst head1)
in uu____1934.FStar_Syntax_Syntax.n)
in (match (uu____1933) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1938 -> begin
false
end))
end)))
end
| uu____1939 -> begin
false
end)
end
| uu____1948 -> begin
false
end)
end
| uu____1949 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___47_1963 -> (match (uu___47_1963) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1964 -> begin
false
end)))))
end
| uu____1965 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1980) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1990) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____2018) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____2027) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___56_2039 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___56_2039.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___56_2039.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___56_2039.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___56_2039.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___48_2052 -> (match (uu___48_2052) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____2053 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____2073 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2081, uu____2082) -> begin
(unascribe e2)
end
| uu____2123 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____2175, uu____2176) -> begin
(ascribe t' k)
end
| uu____2217 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))


let unfold_lazy : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____2243 = (

let uu____2252 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____2252))
in (uu____2243 i.FStar_Syntax_Syntax.lkind i)))


let rec unlazy : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____2311 = (

let uu____2312 = (FStar_Syntax_Subst.compress t)
in uu____2312.FStar_Syntax_Syntax.n)
in (match (uu____2311) with
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____2316 = (unfold_lazy i)
in (FStar_All.pipe_left unlazy uu____2316))
end
| uu____2317 -> begin
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

let uu____2356 = (FStar_Dyn.mkdyn t)
in {FStar_Syntax_Syntax.blob = uu____2356; FStar_Syntax_Syntax.lkind = k; FStar_Syntax_Syntax.typ = typ; FStar_Syntax_Syntax.rng = rng})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (i)) FStar_Pervasives_Native.None rng))))


let canon_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____2368 = (

let uu____2381 = (unascribe t)
in (head_and_args' uu____2381))
in (match (uu____2368) with
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
| uu____2407 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____2413 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____2419 -> begin
false
end))


let injectives : Prims.string Prims.list = ("FStar.Int8.int_to_t")::("FStar.Int16.int_to_t")::("FStar.Int32.int_to_t")::("FStar.Int64.int_to_t")::("FStar.UInt8.uint_to_t")::("FStar.UInt16.uint_to_t")::("FStar.UInt32.uint_to_t")::("FStar.UInt64.uint_to_t")::("FStar.Int8.__int_to_t")::("FStar.Int16.__int_to_t")::("FStar.Int32.__int_to_t")::("FStar.Int64.__int_to_t")::("FStar.UInt8.__uint_to_t")::("FStar.UInt16.__uint_to_t")::("FStar.UInt32.__uint_to_t")::("FStar.UInt64.__uint_to_t")::[]


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___49_2495 -> (match (uu___49_2495) with
| true -> begin
Equal
end
| uu____2496 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___50_2502 -> (match (uu___50_2502) with
| true -> begin
Equal
end
| uu____2503 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____2520 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____2532) -> begin
NotEqual
end
| (uu____2533, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____2534) -> begin
Unknown
end
| (uu____2535, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____2581 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2581) with
| true -> begin
(

let uu____2583 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2641 -> (match (uu____2641) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2667 = (eq_tm a1 a2)
in (eq_inj acc uu____2667))
end)) Equal) uu____2583))
end
| uu____2668 -> begin
NotEqual
end)))
in (

let uu____2669 = (

let uu____2674 = (

let uu____2675 = (unmeta t11)
in uu____2675.FStar_Syntax_Syntax.n)
in (

let uu____2678 = (

let uu____2679 = (unmeta t21)
in uu____2679.FStar_Syntax_Syntax.n)
in ((uu____2674), (uu____2678))))
in (match (uu____2669) with
| (FStar_Syntax_Syntax.Tm_bvar (bv1), FStar_Syntax_Syntax.Tm_bvar (bv2)) -> begin
(equal_if (Prims.op_Equality bv1.FStar_Syntax_Syntax.index bv2.FStar_Syntax_Syntax.index))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____2684), uu____2685) -> begin
(

let uu____2686 = (unlazy t11)
in (eq_tm uu____2686 t21))
end
| (uu____2687, FStar_Syntax_Syntax.Tm_lazy (uu____2688)) -> begin
(

let uu____2689 = (unlazy t21)
in (eq_tm t11 uu____2689))
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))) with
| true -> begin
(equal_data f [] g [])
end
| uu____2706 -> begin
(

let uu____2707 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2707))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2720 = (eq_tm f g)
in (eq_and uu____2720 (fun uu____2723 -> (

let uu____2724 = (eq_univs_list us vs)
in (equal_if uu____2724)))))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2725)), uu____2726) -> begin
Unknown
end
| (uu____2727, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (uu____2728))) -> begin
Unknown
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2731 = (FStar_Const.eq_const c d)
in (equal_iff uu____2731))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1), FStar_Syntax_Syntax.Tm_uvar (u2)) -> begin
(

let uu____2734 = (FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head)
in (equal_if uu____2734))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2779 = (

let uu____2784 = (

let uu____2785 = (un_uinst h1)
in uu____2785.FStar_Syntax_Syntax.n)
in (

let uu____2788 = (

let uu____2789 = (un_uinst h2)
in uu____2789.FStar_Syntax_Syntax.n)
in ((uu____2784), (uu____2788))))
in (match (uu____2779) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((Prims.op_Equality f1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality f2.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
(equal_data f1 args1 f2 args2)
end
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((FStar_Syntax_Syntax.fv_eq f1 f2) && (

let uu____2801 = (

let uu____2802 = (FStar_Syntax_Syntax.lid_of_fv f1)
in (FStar_Ident.string_of_lid uu____2802))
in (FStar_List.mem uu____2801 injectives))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____2803 -> begin
(

let uu____2808 = (eq_tm h1 h2)
in (eq_and uu____2808 (fun uu____2810 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
(match ((Prims.op_Equality (FStar_List.length bs1) (FStar_List.length bs2))) with
| true -> begin
(

let uu____2915 = (FStar_List.zip bs1 bs2)
in (

let uu____2978 = (eq_tm t12 t22)
in (FStar_List.fold_right (fun uu____3015 a -> (match (uu____3015) with
| (b1, b2) -> begin
(eq_and a (fun uu____3108 -> (branch_matches b1 b2)))
end)) uu____2915 uu____2978)))
end
| uu____3109 -> begin
Unknown
end)
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____3112 = (eq_univs u v1)
in (equal_if uu____3112))
end
| (FStar_Syntax_Syntax.Tm_quoted (t12, q1), FStar_Syntax_Syntax.Tm_quoted (t22, q2)) -> begin
(match ((Prims.op_Equality q1 q2)) with
| true -> begin
(eq_tm t12 t22)
end
| uu____3125 -> begin
Unknown
end)
end
| uu____3126 -> begin
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
| (uu____3209, uu____3210) -> begin
false
end))
in (

let uu____3219 = b1
in (match (uu____3219) with
| (p1, w1, t1) -> begin
(

let uu____3253 = b2
in (match (uu____3253) with
| (p2, w2, t2) -> begin
(

let uu____3287 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (match (uu____3287) with
| true -> begin
(

let uu____3288 = ((

let uu____3291 = (eq_tm t1 t2)
in (Prims.op_Equality uu____3291 Equal)) && (related_by (fun t11 t21 -> (

let uu____3300 = (eq_tm t11 t21)
in (Prims.op_Equality uu____3300 Equal))) w1 w2))
in (match (uu____3288) with
| true -> begin
Equal
end
| uu____3301 -> begin
Unknown
end))
end
| uu____3302 -> begin
Unknown
end))
end))
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____3350))::a11, ((b, uu____3353))::b1) -> begin
(

let uu____3407 = (eq_tm a b)
in (match (uu____3407) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____3408 -> begin
Unknown
end))
end
| uu____3409 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3439) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3445, uu____3446) -> begin
(unrefine t2)
end
| uu____3487 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3493 = (

let uu____3494 = (unrefine t)
in uu____3494.FStar_Syntax_Syntax.n)
in (match (uu____3493) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3499) -> begin
(is_unit t1)
end
| uu____3504 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3510 = (

let uu____3511 = (unrefine t)
in uu____3511.FStar_Syntax_Syntax.n)
in (match (uu____3510) with
| FStar_Syntax_Syntax.Tm_type (uu____3514) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____3517) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3539) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3544, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____3562 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____3568 = (

let uu____3569 = (FStar_Syntax_Subst.compress e)
in uu____3569.FStar_Syntax_Syntax.n)
in (match (uu____3568) with
| FStar_Syntax_Syntax.Tm_abs (uu____3572) -> begin
true
end
| uu____3589 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3595 = (

let uu____3596 = (FStar_Syntax_Subst.compress t)
in uu____3596.FStar_Syntax_Syntax.n)
in (match (uu____3595) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3599) -> begin
true
end
| uu____3612 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____3620) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3626, uu____3627) -> begin
(pre_typ t2)
end
| uu____3668 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____3690 = (

let uu____3691 = (un_uinst typ1)
in uu____3691.FStar_Syntax_Syntax.n)
in (match (uu____3690) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____3746 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____3770 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____3788, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_splice (lids, uu____3795) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____3800, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3811, uu____3812, uu____3813, uu____3814, uu____3815) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3825, uu____3826, uu____3827, uu____3828) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3834, uu____3835, uu____3836, uu____3837, uu____3838) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3844, uu____3845) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____3847, uu____3848) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____3851) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____3852) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____3853) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____3866 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lbname : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Range.range = (fun uu___51_3889 -> (match (uu___51_3889) with
| FStar_Util.Inl (x) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| FStar_Util.Inr (fv) -> begin
(FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let range_of_arg : 'Auu____3902 'Auu____3903 . ('Auu____3902 FStar_Syntax_Syntax.syntax * 'Auu____3903)  ->  FStar_Range.range = (fun uu____3914 -> (match (uu____3914) with
| (hd1, uu____3922) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____3935 'Auu____3936 . ('Auu____3935 FStar_Syntax_Syntax.syntax * 'Auu____3936) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (match (args) with
| [] -> begin
f
end
| uu____4027 -> begin
(

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r))
end))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____4087 = (FStar_Ident.range_of_lid l)
in (

let uu____4088 = (

let uu____4097 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (FStar_Syntax_Syntax.mk uu____4097))
in (uu____4088 FStar_Pervasives_Native.None uu____4087)))
end
| uu____4105 -> begin
(

let e = (

let uu____4117 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____4117 args))
in (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____4132 = (

let uu____4137 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____4137), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4132))
end
| uu____4138 -> begin
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
| uu____4167 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____4188 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____4188) with
| true -> begin
(

let uu____4189 = (

let uu____4194 = (

let uu____4195 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____4195))
in (

let uu____4196 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____4194), (uu____4196))))
in (FStar_Ident.mk_ident uu____4189))
end
| uu____4197 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___57_4199 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___57_4199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___57_4199.FStar_Syntax_Syntax.sort})
in (

let uu____4200 = (mk_field_projector_name_from_ident lid nm)
in ((uu____4200), (y))))))


let ses_of_sigbundle : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4211) -> begin
ses
end
| uu____4220 -> begin
(failwith "ses_of_sigbundle: not a Sig_bundle")
end))


let eff_decl_of_new_effect : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.eff_decl = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
ne
end
| uu____4229 -> begin
(failwith "eff_decl_of_new_effect: not a Sig_new_effect")
end))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun uv t -> (

let uu____4240 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____4240) with
| FStar_Pervasives_Native.Some (uu____4243) -> begin
(

let uu____4244 = (

let uu____4245 = (

let uu____4246 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____4246))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____4245))
in (failwith uu____4244))
end
| uu____4247 -> begin
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
| uu____4322 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____4367 = (

let uu___58_4368 = rc
in (

let uu____4369 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___58_4368.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____4369; FStar_Syntax_Syntax.residual_flags = uu___58_4368.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____4367))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____4384 -> begin
(

let body = (

let uu____4386 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____4386))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____4416 = (

let uu____4423 = (

let uu____4424 = (

let uu____4441 = (

let uu____4448 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____4448 bs'))
in (

let uu____4459 = (close_lopt lopt')
in ((uu____4441), (t1), (uu____4459))))
in FStar_Syntax_Syntax.Tm_abs (uu____4424))
in (FStar_Syntax_Syntax.mk uu____4423))
in (uu____4416 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____4475 -> begin
(

let uu____4482 = (

let uu____4489 = (

let uu____4490 = (

let uu____4507 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4514 = (close_lopt lopt)
in ((uu____4507), (body), (uu____4514))))
in FStar_Syntax_Syntax.Tm_abs (uu____4490))
in (FStar_Syntax_Syntax.mk uu____4489))
in (uu____4482 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____4564 -> begin
(

let uu____4571 = (

let uu____4578 = (

let uu____4579 = (

let uu____4592 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____4599 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____4592), (uu____4599))))
in FStar_Syntax_Syntax.Tm_arrow (uu____4579))
in (FStar_Syntax_Syntax.mk uu____4578))
in (uu____4571 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____4644 = (

let uu____4645 = (FStar_Syntax_Subst.compress t)
in uu____4645.FStar_Syntax_Syntax.n)
in (match (uu____4644) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____4671) -> begin
(

let uu____4680 = (

let uu____4681 = (FStar_Syntax_Subst.compress tres)
in uu____4681.FStar_Syntax_Syntax.n)
in (match (uu____4680) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____4716 -> begin
t
end))
end
| uu____4717 -> begin
t
end)
end
| uu____4718 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____4735 = (

let uu____4736 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____4736 t.FStar_Syntax_Syntax.pos))
in (

let uu____4737 = (

let uu____4744 = (

let uu____4745 = (

let uu____4752 = (

let uu____4755 = (

let uu____4756 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____4756)::[])
in (FStar_Syntax_Subst.close uu____4755 t))
in ((b), (uu____4752)))
in FStar_Syntax_Syntax.Tm_refine (uu____4745))
in (FStar_Syntax_Syntax.mk uu____4744))
in (uu____4737 FStar_Pervasives_Native.None uu____4735))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4823 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4823) with
| (bs1, c1) -> begin
(

let uu____4840 = (is_total_comp c1)
in (match (uu____4840) with
| true -> begin
(

let uu____4851 = (arrow_formals_comp (comp_result c1))
in (match (uu____4851) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____4896 -> begin
((bs1), (c1))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____4903; FStar_Syntax_Syntax.index = uu____4904; FStar_Syntax_Syntax.sort = k2}, uu____4906) -> begin
(arrow_formals_comp k2)
end
| uu____4913 -> begin
(

let uu____4914 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4914)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____4942 = (arrow_formals_comp k)
in (match (uu____4942) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____5024 = (

let uu___59_5025 = rc
in (

let uu____5026 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___59_5025.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5026; FStar_Syntax_Syntax.residual_flags = uu___59_5025.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____5024))
end
| uu____5035 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____5067 = (

let uu____5068 = (

let uu____5071 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____5071))
in uu____5068.FStar_Syntax_Syntax.n)
in (match (uu____5067) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____5111 = (aux t2 what)
in (match (uu____5111) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____5171 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____5184 = (aux t FStar_Pervasives_Native.None)
in (match (uu____5184) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____5226 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____5226) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def lbattrs pos -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = lbattrs; FStar_Syntax_Syntax.lbpos = pos})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def attrs pos -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____5387) -> begin
def
end
| (uu____5398, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____5410) -> begin
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


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____5496 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____5496) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____5525 -> begin
(

let t' = (arrow binders c)
in (

let uu____5535 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____5535) with
| (uvs1, t'1) -> begin
(

let uu____5554 = (

let uu____5555 = (FStar_Syntax_Subst.compress t'1)
in uu____5555.FStar_Syntax_Syntax.n)
in (match (uu____5554) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____5596 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____5615 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5622 -> begin
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

let uu____5670 = (

let uu____5671 = (pre_typ t)
in uu____5671.FStar_Syntax_Syntax.n)
in (match (uu____5670) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____5675 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____5686 = (

let uu____5687 = (pre_typ t)
in uu____5687.FStar_Syntax_Syntax.n)
in (match (uu____5686) with
| FStar_Syntax_Syntax.Tm_fvar (uu____5690) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____5692) -> begin
(is_constructed_typ t1 lid)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5714) -> begin
(is_constructed_typ t1 lid)
end
| uu____5719 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____5730) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____5731) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____5732) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5734) -> begin
(get_tycon t2)
end
| uu____5755 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5769 = (

let uu____5770 = (un_uinst t)
in uu____5770.FStar_Syntax_Syntax.n)
in (match (uu____5769) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____5774 -> begin
false
end)))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____5781 = (

let uu____5784 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____5784))
in (match (uu____5781) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____5797 -> begin
false
end))
end
| uu____5800 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____5813 -> (

let u = (

let uu____5819 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_5 -> FStar_Syntax_Syntax.U_unif (_0_5)) uu____5819))
in (

let uu____5836 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____5836), (u)))))


let attr_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun a a' -> (

let uu____5847 = (eq_tm a a')
in (match (uu____5847) with
| Equal -> begin
true
end
| uu____5848 -> begin
false
end)))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____5851 = (

let uu____5858 = (

let uu____5859 = (

let uu____5860 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____5860 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____5859))
in (FStar_Syntax_Syntax.mk uu____5858))
in (uu____5851 FStar_Pervasives_Native.None FStar_Range.dummyRange))


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


let mk_conj_opt : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____5939 = (

let uu____5942 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____5943 = (

let uu____5950 = (

let uu____5951 = (

let uu____5966 = (

let uu____5975 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____5982 = (

let uu____5991 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____5991)::[])
in (uu____5975)::uu____5982))
in ((tand), (uu____5966)))
in FStar_Syntax_Syntax.Tm_app (uu____5951))
in (FStar_Syntax_Syntax.mk uu____5950))
in (uu____5943 FStar_Pervasives_Native.None uu____5942)))
in FStar_Pervasives_Native.Some (uu____5939))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____6060 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____6061 = (

let uu____6068 = (

let uu____6069 = (

let uu____6084 = (

let uu____6093 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____6100 = (

let uu____6109 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____6109)::[])
in (uu____6093)::uu____6100))
in ((op_t), (uu____6084)))
in FStar_Syntax_Syntax.Tm_app (uu____6069))
in (FStar_Syntax_Syntax.mk uu____6068))
in (uu____6061 FStar_Pervasives_Native.None uu____6060))))


let mk_neg : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____6158 = (

let uu____6165 = (

let uu____6166 = (

let uu____6181 = (

let uu____6190 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____6190)::[])
in ((t_not), (uu____6181)))
in FStar_Syntax_Syntax.Tm_app (uu____6166))
in (FStar_Syntax_Syntax.mk uu____6165))
in (uu____6158 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
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

let uu____6375 = (

let uu____6382 = (

let uu____6383 = (

let uu____6398 = (

let uu____6407 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6407)::[])
in ((b2t_v), (uu____6398)))
in FStar_Syntax_Syntax.Tm_app (uu____6383))
in (FStar_Syntax_Syntax.mk uu____6382))
in (uu____6375 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____6459 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6460 = (

let uu____6467 = (

let uu____6468 = (

let uu____6483 = (

let uu____6492 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6499 = (

let uu____6508 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6508)::[])
in (uu____6492)::uu____6499))
in ((teq), (uu____6483)))
in FStar_Syntax_Syntax.Tm_app (uu____6468))
in (FStar_Syntax_Syntax.mk uu____6467))
in (uu____6460 FStar_Pervasives_Native.None uu____6459))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____6567 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____6568 = (

let uu____6575 = (

let uu____6576 = (

let uu____6591 = (

let uu____6600 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6607 = (

let uu____6616 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____6623 = (

let uu____6632 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____6632)::[])
in (uu____6616)::uu____6623))
in (uu____6600)::uu____6607))
in ((eq_inst), (uu____6591)))
in FStar_Syntax_Syntax.Tm_app (uu____6576))
in (FStar_Syntax_Syntax.mk uu____6575))
in (uu____6568 FStar_Pervasives_Native.None uu____6567)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6699 = (

let uu____6706 = (

let uu____6707 = (

let uu____6722 = (

let uu____6731 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6738 = (

let uu____6747 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____6754 = (

let uu____6763 = (FStar_Syntax_Syntax.as_arg t')
in (uu____6763)::[])
in (uu____6747)::uu____6754))
in (uu____6731)::uu____6738))
in ((t_has_type1), (uu____6722)))
in FStar_Syntax_Syntax.Tm_app (uu____6707))
in (FStar_Syntax_Syntax.mk uu____6706))
in (uu____6699 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let mk_with_type : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u t e -> (

let t_with_type = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (

let t_with_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_with_type), ((u)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____6830 = (

let uu____6837 = (

let uu____6838 = (

let uu____6853 = (

let uu____6862 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____6869 = (

let uu____6878 = (FStar_Syntax_Syntax.as_arg e)
in (uu____6878)::[])
in (uu____6862)::uu____6869))
in ((t_with_type1), (uu____6853)))
in FStar_Syntax_Syntax.Tm_app (uu____6838))
in (FStar_Syntax_Syntax.mk uu____6837))
in (uu____6830 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____6918 = (

let uu____6925 = (

let uu____6926 = (

let uu____6933 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____6933), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6926))
in (FStar_Syntax_Syntax.mk uu____6925))
in (uu____6918 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____6946 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____6959) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____6970) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____6946) with
| (eff_name, flags1) -> begin
(FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags1 (fun uu____6991 -> c0))
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____7069 = (

let uu____7076 = (

let uu____7077 = (

let uu____7092 = (

let uu____7101 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____7108 = (

let uu____7117 = (

let uu____7124 = (

let uu____7125 = (

let uu____7126 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7126)::[])
in (abs uu____7125 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____7124))
in (uu____7117)::[])
in (uu____7101)::uu____7108))
in ((fa), (uu____7092)))
in FStar_Syntax_Syntax.Tm_app (uu____7077))
in (FStar_Syntax_Syntax.mk uu____7076))
in (uu____7069 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____7231 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____7231) with
| true -> begin
f1
end
| uu____7232 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____7242) -> begin
true
end
| uu____7243 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____7288 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____7288), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____7316 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____7316), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____7329 = (

let uu____7330 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____7330))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____7329)))))


let mk_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____7404 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____7407 = (

let uu____7416 = (FStar_Syntax_Syntax.as_arg p)
in (uu____7416)::[])
in (mk_app uu____7404 uu____7407)))))


let mk_auto_squash : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun u p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)
in (

let uu____7448 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((u)::[]))
in (

let uu____7451 = (

let uu____7460 = (FStar_Syntax_Syntax.as_arg p)
in (uu____7460)::[])
in (mk_app uu____7448 uu____7451)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____7488 = (head_and_args t)
in (match (uu____7488) with
| (head1, args) -> begin
(

let uu____7529 = (

let uu____7542 = (

let uu____7543 = (un_uinst head1)
in uu____7543.FStar_Syntax_Syntax.n)
in ((uu____7542), (args)))
in (match (uu____7529) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____7560))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____7612 = (

let uu____7617 = (

let uu____7618 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____7618)::[])
in (FStar_Syntax_Subst.open_term uu____7617 p))
in (match (uu____7612) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7659 -> begin
(failwith "impossible")
end)
in (

let uu____7664 = (

let uu____7665 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____7665))
in (match (uu____7664) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7674 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____7675 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____7678 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7706 = (head_and_args t)
in (match (uu____7706) with
| (head1, args) -> begin
(

let uu____7751 = (

let uu____7764 = (

let uu____7765 = (FStar_Syntax_Subst.compress head1)
in uu____7765.FStar_Syntax_Syntax.n)
in ((uu____7764), (args)))
in (match (uu____7751) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7785; FStar_Syntax_Syntax.vars = uu____7786}, (u)::[]), ((t1, uu____7789))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7826 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_auto_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option = (fun t -> (

let uu____7858 = (head_and_args t)
in (match (uu____7858) with
| (head1, args) -> begin
(

let uu____7903 = (

let uu____7916 = (

let uu____7917 = (FStar_Syntax_Subst.compress head1)
in uu____7917.FStar_Syntax_Syntax.n)
in ((uu____7916), (args)))
in (match (uu____7903) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7937; FStar_Syntax_Syntax.vars = uu____7938}, (u)::[]), ((t1, uu____7941))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid) -> begin
FStar_Pervasives_Native.Some (((u), (t1)))
end
| uu____7978 -> begin
FStar_Pervasives_Native.None
end))
end)))


let is_sub_singleton : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____8002 = (

let uu____8017 = (unmeta t)
in (head_and_args uu____8017))
in (match (uu____8002) with
| (head1, uu____8019) -> begin
(

let uu____8040 = (

let uu____8041 = (un_uinst head1)
in uu____8041.FStar_Syntax_Syntax.n)
in (match (uu____8040) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.ite_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq3_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.haseq_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.precedes_lid))
end
| uu____8045 -> begin
false
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____8063 = (

let uu____8074 = (

let uu____8075 = (FStar_Syntax_Subst.compress t)
in uu____8075.FStar_Syntax_Syntax.n)
in (match (uu____8074) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____8178 = (

let uu____8187 = (

let uu____8188 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____8188))
in ((b), (uu____8187)))
in FStar_Pervasives_Native.Some (uu____8178))
end
| uu____8201 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____8063 (fun uu____8233 -> (match (uu____8233) with
| (b, c) -> begin
(

let uu____8262 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____8262) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____8309 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____8336 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____8336)))


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
| uu____8384 -> begin
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
| uu____8422 -> begin
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
| uu____8458 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____8495)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____8507)) -> begin
(unmeta_monadic t)
end
| uu____8520 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____8604 -> (match (uu____8604) with
| (lid, arity) -> begin
(

let uu____8613 = (

let uu____8628 = (unmeta_monadic f2)
in (head_and_args uu____8628))
in (match (uu____8613) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____8654 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____8654) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____8667 -> begin
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

let uu____8723 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____8723)))
end
| uu____8734 -> begin
(([]), (t1))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____8772 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____8789 = (head_and_args t1)
in (match (uu____8789) with
| (t2, args) -> begin
(

let uu____8836 = (un_uinst t2)
in (

let uu____8837 = (FStar_All.pipe_right args (FStar_List.map (fun uu____8868 -> (match (uu____8868) with
| (t3, imp) -> begin
(

let uu____8879 = (unascribe t3)
in ((uu____8879), (imp)))
end))))
in ((uu____8836), (uu____8837))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____8920 = (

let uu____8941 = (flat t1)
in ((qopt), (uu____8941)))
in (match (uu____8920) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____8976; FStar_Syntax_Syntax.vars = uu____8977}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____8980); FStar_Syntax_Syntax.pos = uu____8981; FStar_Syntax_Syntax.vars = uu____8982}, uu____8983))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____9060; FStar_Syntax_Syntax.vars = uu____9061}, (uu____9062)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____9065); FStar_Syntax_Syntax.pos = uu____9066; FStar_Syntax_Syntax.vars = uu____9067}, uu____9068))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____9156; FStar_Syntax_Syntax.vars = uu____9157}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____9160); FStar_Syntax_Syntax.pos = uu____9161; FStar_Syntax_Syntax.vars = uu____9162}, uu____9163))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____9234 = (

let uu____9237 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____9237))
in (aux uu____9234 ((b)::out) t2))
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____9243; FStar_Syntax_Syntax.vars = uu____9244}, (uu____9245)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____9248); FStar_Syntax_Syntax.pos = uu____9249; FStar_Syntax_Syntax.vars = uu____9250}, uu____9251))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(

let uu____9334 = (

let uu____9337 = (is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in FStar_Pervasives_Native.Some (uu____9337))
in (aux uu____9334 ((b)::out) t2))
end
| (FStar_Pervasives_Native.Some (b), uu____9343) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____9385 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____9385) with
| (bs1, t2) -> begin
(

let uu____9394 = (patterns t2)
in (match (uu____9394) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____9435 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____9436 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____9508 = (un_squash t)
in (FStar_Util.bind_opt uu____9508 (fun t1 -> (

let uu____9524 = (head_and_args' t1)
in (match (uu____9524) with
| (hd1, args) -> begin
(

let uu____9557 = (

let uu____9562 = (

let uu____9563 = (un_uinst hd1)
in uu____9563.FStar_Syntax_Syntax.n)
in ((uu____9562), ((FStar_List.length args))))
in (match (uu____9557) with
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
| uu____9582 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____9611 = (un_squash t)
in (FStar_Util.bind_opt uu____9611 (fun t1 -> (

let uu____9626 = (arrow_one t1)
in (match (uu____9626) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____9641 = (

let uu____9642 = (is_tot_or_gtot_comp c)
in (not (uu____9642)))
in (match (uu____9641) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9645 -> begin
(

let q = (

let uu____9649 = (comp_to_comp_typ_nouniv c)
in uu____9649.FStar_Syntax_Syntax.result_typ)
in (

let uu____9650 = (is_free_in (FStar_Pervasives_Native.fst b) q)
in (match (uu____9650) with
| true -> begin
(

let uu____9653 = (patterns q)
in (match (uu____9653) with
| (pats, q1) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b)::[]), (pats), (q1))))))
end))
end
| uu____9704 -> begin
(

let uu____9705 = (

let uu____9706 = (

let uu____9711 = (

let uu____9712 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (

let uu____9719 = (

let uu____9728 = (FStar_Syntax_Syntax.as_arg q)
in (uu____9728)::[])
in (uu____9712)::uu____9719))
in ((FStar_Parser_Const.imp_lid), (uu____9711)))
in BaseConn (uu____9706))
in FStar_Pervasives_Native.Some (uu____9705))
end)))
end))
end
| uu____9753 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____9761 = (un_squash t)
in (FStar_Util.bind_opt uu____9761 (fun t1 -> (

let uu____9792 = (head_and_args' t1)
in (match (uu____9792) with
| (hd1, args) -> begin
(

let uu____9825 = (

let uu____9838 = (

let uu____9839 = (un_uinst hd1)
in uu____9839.FStar_Syntax_Syntax.n)
in ((uu____9838), (args)))
in (match (uu____9825) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____9854))::((a2, uu____9856))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____9891 = (

let uu____9892 = (FStar_Syntax_Subst.compress a2)
in uu____9892.FStar_Syntax_Syntax.n)
in (match (uu____9891) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____9899) -> begin
(

let uu____9926 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____9926) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9965 -> begin
(failwith "impossible")
end)
in (

let uu____9970 = (patterns q1)
in (match (uu____9970) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____10021 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10022 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____10043 = (destruct_sq_forall phi)
in (match (uu____10043) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____10057 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____10063 = (destruct_sq_exists phi)
in (match (uu____10063) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____10077 -> begin
f1
end))
end
| uu____10080 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____10084 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____10084 (fun uu____10089 -> (

let uu____10090 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____10090 (fun uu____10095 -> (

let uu____10096 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____10096 (fun uu____10101 -> (

let uu____10102 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____10102 (fun uu____10107 -> (

let uu____10108 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____10108 (fun uu____10112 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let unthunk_lemma_post : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let uu____10124 = (

let uu____10125 = (FStar_Syntax_Subst.compress t)
in uu____10125.FStar_Syntax_Syntax.n)
in (match (uu____10124) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], e, uu____10132) -> begin
(

let uu____10159 = (FStar_Syntax_Subst.open_term ((b)::[]) e)
in (match (uu____10159) with
| (bs, e1) -> begin
(

let b1 = (FStar_List.hd bs)
in (

let uu____10185 = (is_free_in (FStar_Pervasives_Native.fst b1) e1)
in (match (uu____10185) with
| true -> begin
(

let uu____10188 = (

let uu____10197 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____10197)::[])
in (mk_app t uu____10188))
end
| uu____10216 -> begin
e1
end)))
end))
end
| uu____10217 -> begin
(

let uu____10218 = (

let uu____10227 = (FStar_Syntax_Syntax.as_arg exp_unit)
in (uu____10227)::[])
in (mk_app t uu____10218))
end)))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a pos -> (

let lb = (

let uu____10262 = (

let uu____10267 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____10267))
in (

let uu____10268 = (

let uu____10269 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____10269))
in (

let uu____10272 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____10262 a.FStar_Syntax_Syntax.action_univs uu____10268 FStar_Parser_Const.effect_Tot_lid uu____10272 [] pos))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____10295 = (

let uu____10302 = (

let uu____10303 = (

let uu____10318 = (

let uu____10327 = (FStar_Syntax_Syntax.as_arg t)
in (uu____10327)::[])
in ((reify_), (uu____10318)))
in FStar_Syntax_Syntax.Tm_app (uu____10303))
in (FStar_Syntax_Syntax.mk uu____10302))
in (uu____10295 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____10365) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____10391 = (unfold_lazy i)
in (delta_qualifier uu____10391))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____10393) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____10394) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____10395) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____10418) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____10419) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_quoted (uu____10420) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____10427) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____10428) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____10442) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____10447; FStar_Syntax_Syntax.index = uu____10448; FStar_Syntax_Syntax.sort = t2}, uu____10450) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____10458) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____10464, uu____10465) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____10507) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____10528, t2, uu____10530) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____10551, t2) -> begin
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

let uu____10581 = (delta_qualifier t)
in (incr_delta_depth uu____10581)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____10587 = (

let uu____10588 = (FStar_Syntax_Subst.compress t)
in uu____10588.FStar_Syntax_Syntax.n)
in (match (uu____10587) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____10591 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____10605 = (

let uu____10620 = (unmeta e)
in (head_and_args uu____10620))
in (match (uu____10605) with
| (head1, args) -> begin
(

let uu____10647 = (

let uu____10660 = (

let uu____10661 = (un_uinst head1)
in uu____10661.FStar_Syntax_Syntax.n)
in ((uu____10660), (args)))
in (match (uu____10647) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____10677) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10697)::((hd1, uu____10699))::((tl1, uu____10701))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____10748 = (

let uu____10751 = (

let uu____10754 = (list_elements tl1)
in (FStar_Util.must uu____10754))
in (hd1)::uu____10751)
in FStar_Pervasives_Native.Some (uu____10748))
end
| uu____10763 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____10785 . ('Auu____10785  ->  'Auu____10785)  ->  'Auu____10785 Prims.list  ->  'Auu____10785 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____10810 = (f a)
in (uu____10810)::[])
end
| (x)::xs -> begin
(

let uu____10815 = (apply_last f xs)
in (x)::uu____10815)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____10861 = (

let uu____10868 = (

let uu____10869 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____10869))
in (FStar_Syntax_Syntax.mk uu____10868))
in (uu____10861 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____10886 = (

let uu____10891 = (

let uu____10892 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10892 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10891 args))
in (uu____10886 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____10908 = (

let uu____10913 = (

let uu____10914 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____10914 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____10913 args))
in (uu____10908 FStar_Pervasives_Native.None pos)))
in (

let uu____10917 = (

let uu____10918 = (

let uu____10919 = (FStar_Syntax_Syntax.iarg typ)
in (uu____10919)::[])
in (nil uu____10918 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____10947 = (

let uu____10948 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____10955 = (

let uu____10964 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____10971 = (

let uu____10980 = (FStar_Syntax_Syntax.as_arg a)
in (uu____10980)::[])
in (uu____10964)::uu____10971))
in (uu____10948)::uu____10955))
in (cons1 uu____10947 t.FStar_Syntax_Syntax.pos))) l uu____10917))))))


let uvar_from_id : Prims.int  ->  (FStar_Syntax_Syntax.binding Prims.list * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id1 uu____11038 -> (match (uu____11038) with
| (gamma, bs, t) -> begin
(

let ctx_u = (

let uu____11081 = (FStar_Syntax_Unionfind.from_id id1)
in {FStar_Syntax_Syntax.ctx_uvar_head = uu____11081; FStar_Syntax_Syntax.ctx_uvar_gamma = gamma; FStar_Syntax_Syntax.ctx_uvar_binders = bs; FStar_Syntax_Syntax.ctx_uvar_typ = t; FStar_Syntax_Syntax.ctx_uvar_reason = ""; FStar_Syntax_Syntax.ctx_uvar_should_check = true; FStar_Syntax_Syntax.ctx_uvar_range = FStar_Range.dummyRange})
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u)) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____11155 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____11262 -> begin
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
| uu____11417 -> begin
false
end))


let debug_term_eq : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let check : Prims.string  ->  Prims.bool  ->  Prims.bool = (fun msg cond -> (match (cond) with
| true -> begin
true
end
| uu____11449 -> begin
((

let uu____11451 = (FStar_ST.op_Bang debug_term_eq)
in (match (uu____11451) with
| true -> begin
(FStar_Util.print1 ">>> term_eq failing: %s\n" msg)
end
| uu____11475 -> begin
()
end));
false;
)
end))


let fail : Prims.string  ->  Prims.bool = (fun msg -> (check msg false))


let rec term_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun dbg t1 t2 -> (

let t11 = (

let uu____11639 = (unmeta_safe t1)
in (canon_app uu____11639))
in (

let t21 = (

let uu____11645 = (unmeta_safe t2)
in (canon_app uu____11645))
in (

let uu____11648 = (

let uu____11653 = (

let uu____11654 = (

let uu____11657 = (un_uinst t11)
in (FStar_Syntax_Subst.compress uu____11657))
in uu____11654.FStar_Syntax_Syntax.n)
in (

let uu____11658 = (

let uu____11659 = (

let uu____11662 = (un_uinst t21)
in (FStar_Syntax_Subst.compress uu____11662))
in uu____11659.FStar_Syntax_Syntax.n)
in ((uu____11653), (uu____11658))))
in (match (uu____11648) with
| (FStar_Syntax_Syntax.Tm_uinst (uu____11663), uu____11664) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11671, FStar_Syntax_Syntax.Tm_uinst (uu____11672)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_delayed (uu____11679), uu____11680) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11705, FStar_Syntax_Syntax.Tm_delayed (uu____11706)) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (FStar_Syntax_Syntax.Tm_ascribed (uu____11731), uu____11732) -> begin
(failwith "term_eq: impossible, should have been removed")
end
| (uu____11759, FStar_Syntax_Syntax.Tm_ascribed (uu____11760)) -> begin
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

let uu____11793 = (FStar_Syntax_Syntax.fv_eq x y)
in (check "fvar" uu____11793))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(

let uu____11796 = (FStar_Const.eq_const c1 c2)
in (check "const" uu____11796))
end
| (FStar_Syntax_Syntax.Tm_type (uu____11797), FStar_Syntax_Syntax.Tm_type (uu____11798)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((

let uu____11847 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "abs binders" uu____11847)) && (

let uu____11853 = (term_eq_dbg dbg t12 t22)
in (check "abs bodies" uu____11853)))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((

let uu____11892 = (eqlist (binder_eq_dbg dbg) b1 b2)
in (check "arrow binders" uu____11892)) && (

let uu____11898 = (comp_eq_dbg dbg c1 c2)
in (check "arrow comp" uu____11898)))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((check "refine bv" (Prims.op_Equality b1.FStar_Syntax_Syntax.index b2.FStar_Syntax_Syntax.index)) && (

let uu____11912 = (term_eq_dbg dbg t12 t22)
in (check "refine formula" uu____11912)))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((

let uu____11959 = (term_eq_dbg dbg f1 f2)
in (check "app head" uu____11959)) && (

let uu____11961 = (eqlist (arg_eq_dbg dbg) a1 a2)
in (check "app args" uu____11961)))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((

let uu____12046 = (term_eq_dbg dbg t12 t22)
in (check "match head" uu____12046)) && (

let uu____12048 = (eqlist (branch_eq_dbg dbg) bs1 bs2)
in (check "match branches" uu____12048)))
end
| (FStar_Syntax_Syntax.Tm_lazy (uu____12063), uu____12064) -> begin
(

let uu____12065 = (

let uu____12066 = (unlazy t11)
in (term_eq_dbg dbg uu____12066 t21))
in (check "lazy_l" uu____12065))
end
| (uu____12067, FStar_Syntax_Syntax.Tm_lazy (uu____12068)) -> begin
(

let uu____12069 = (

let uu____12070 = (unlazy t21)
in (term_eq_dbg dbg t11 uu____12070))
in (check "lazy_r" uu____12069))
end
| (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12), FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) -> begin
(((check "let flag" (Prims.op_Equality b1 b2)) && (

let uu____12106 = (eqlist (letbinding_eq_dbg dbg) lbs1 lbs2)
in (check "let lbs" uu____12106))) && (

let uu____12108 = (term_eq_dbg dbg t12 t22)
in (check "let body" uu____12108)))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1), FStar_Syntax_Syntax.Tm_uvar (u2)) -> begin
(check "uvar" (Prims.op_Equality u1.FStar_Syntax_Syntax.ctx_uvar_head u2.FStar_Syntax_Syntax.ctx_uvar_head))
end
| (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1), FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) -> begin
((check "tm_quoted qi" (Prims.op_Equality qi1 qi2)) && (

let uu____12134 = (term_eq_dbg dbg qt1 qt2)
in (check "tm_quoted payload" uu____12134)))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta (t22, m2)) -> begin
(match (((m1), (m2))) with
| (FStar_Syntax_Syntax.Meta_monadic (n1, ty1), FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) -> begin
((

let uu____12161 = (FStar_Ident.lid_equals n1 n2)
in (check "meta_monadic lid" uu____12161)) && (

let uu____12163 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic type" uu____12163)))
end
| (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1), FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) -> begin
(((

let uu____12180 = (FStar_Ident.lid_equals s1 s2)
in (check "meta_monadic_lift src" uu____12180)) && (

let uu____12182 = (FStar_Ident.lid_equals t13 t23)
in (check "meta_monadic_lift tgt" uu____12182))) && (

let uu____12184 = (term_eq_dbg dbg ty1 ty2)
in (check "meta_monadic_lift type" uu____12184)))
end
| uu____12185 -> begin
(fail "metas")
end)
end
| (FStar_Syntax_Syntax.Tm_unknown, uu____12190) -> begin
(fail "unk")
end
| (uu____12191, FStar_Syntax_Syntax.Tm_unknown) -> begin
(fail "unk")
end
| (FStar_Syntax_Syntax.Tm_bvar (uu____12192), uu____12193) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_name (uu____12194), uu____12195) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_fvar (uu____12196), uu____12197) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_constant (uu____12198), uu____12199) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_type (uu____12200), uu____12201) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_abs (uu____12202), uu____12203) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_arrow (uu____12220), uu____12221) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_refine (uu____12234), uu____12235) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_app (uu____12242), uu____12243) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_match (uu____12258), uu____12259) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_let (uu____12282), uu____12283) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_uvar (uu____12296), uu____12297) -> begin
(fail "bottom")
end
| (FStar_Syntax_Syntax.Tm_meta (uu____12298), uu____12299) -> begin
(fail "bottom")
end
| (uu____12306, FStar_Syntax_Syntax.Tm_bvar (uu____12307)) -> begin
(fail "bottom")
end
| (uu____12308, FStar_Syntax_Syntax.Tm_name (uu____12309)) -> begin
(fail "bottom")
end
| (uu____12310, FStar_Syntax_Syntax.Tm_fvar (uu____12311)) -> begin
(fail "bottom")
end
| (uu____12312, FStar_Syntax_Syntax.Tm_constant (uu____12313)) -> begin
(fail "bottom")
end
| (uu____12314, FStar_Syntax_Syntax.Tm_type (uu____12315)) -> begin
(fail "bottom")
end
| (uu____12316, FStar_Syntax_Syntax.Tm_abs (uu____12317)) -> begin
(fail "bottom")
end
| (uu____12334, FStar_Syntax_Syntax.Tm_arrow (uu____12335)) -> begin
(fail "bottom")
end
| (uu____12348, FStar_Syntax_Syntax.Tm_refine (uu____12349)) -> begin
(fail "bottom")
end
| (uu____12356, FStar_Syntax_Syntax.Tm_app (uu____12357)) -> begin
(fail "bottom")
end
| (uu____12372, FStar_Syntax_Syntax.Tm_match (uu____12373)) -> begin
(fail "bottom")
end
| (uu____12396, FStar_Syntax_Syntax.Tm_let (uu____12397)) -> begin
(fail "bottom")
end
| (uu____12410, FStar_Syntax_Syntax.Tm_uvar (uu____12411)) -> begin
(fail "bottom")
end
| (uu____12412, FStar_Syntax_Syntax.Tm_meta (uu____12413)) -> begin
(fail "bottom")
end)))))
and arg_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg a1 a2 -> (eqprod (fun t1 t2 -> (

let uu____12440 = (term_eq_dbg dbg t1 t2)
in (check "arg tm" uu____12440))) (fun q1 q2 -> (check "arg qual" (Prims.op_Equality q1 q2))) a1 a2))
and binder_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun dbg b1 b2 -> (eqprod (fun b11 b21 -> (

let uu____12461 = (term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)
in (check "binder sort" uu____12461))) (fun q1 q2 -> (check "binder qual" (Prims.op_Equality q1 q2))) b1 b2))
and lcomp_eq_dbg : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> (fail "lcomp"))
and residual_eq_dbg : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> (fail "residual"))
and comp_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun dbg c1 c2 -> (

let c11 = (comp_to_comp_typ_nouniv c1)
in (

let c21 = (comp_to_comp_typ_nouniv c2)
in (((

let uu____12481 = (FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)
in (check "comp eff" uu____12481)) && (

let uu____12483 = (term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)
in (check "comp result typ" uu____12483))) && true))))
and eq_flags_dbg : Prims.bool  ->  FStar_Syntax_Syntax.cflags  ->  FStar_Syntax_Syntax.cflags  ->  Prims.bool = (fun dbg f1 f2 -> true)
and branch_eq_dbg : Prims.bool  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun dbg uu____12488 uu____12489 -> (match (((uu____12488), (uu____12489))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
(((

let uu____12614 = (FStar_Syntax_Syntax.eq_pat p1 p2)
in (check "branch pat" uu____12614)) && (

let uu____12616 = (term_eq_dbg dbg t1 t2)
in (check "branch body" uu____12616))) && (

let uu____12618 = (match (((w1), (w2))) with
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(term_eq_dbg dbg x y)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
true
end
| uu____12633 -> begin
false
end)
in (check "branch when" uu____12618)))
end))
and letbinding_eq_dbg : Prims.bool  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding  ->  Prims.bool = (fun dbg lb1 lb2 -> (((

let uu____12647 = (eqsum (fun bv1 bv2 -> true) FStar_Syntax_Syntax.fv_eq lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname)
in (check "lb bv" uu____12647)) && (

let uu____12653 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp lb2.FStar_Syntax_Syntax.lbtyp)
in (check "lb typ" uu____12653))) && (

let uu____12655 = (term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef lb2.FStar_Syntax_Syntax.lbdef)
in (check "lb def" uu____12655))))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let r = (

let uu____12667 = (FStar_ST.op_Bang debug_term_eq)
in (term_eq_dbg uu____12667 t1 t2))
in ((FStar_ST.op_Colon_Equals debug_term_eq false);
r;
)))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12720) -> begin
(

let uu____12745 = (

let uu____12746 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____12746))
in ((Prims.parse_int "1") + uu____12745))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____12748 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12748))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____12750 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____12750))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____12757 = (sizeof t1)
in ((FStar_List.length us) + uu____12757))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12760) -> begin
(

let uu____12781 = (sizeof t1)
in (

let uu____12782 = (FStar_List.fold_left (fun acc uu____12793 -> (match (uu____12793) with
| (bv, uu____12799) -> begin
(

let uu____12800 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____12800))
end)) (Prims.parse_int "0") bs)
in (uu____12781 + uu____12782)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____12823 = (sizeof hd1)
in (

let uu____12824 = (FStar_List.fold_left (fun acc uu____12835 -> (match (uu____12835) with
| (arg, uu____12841) -> begin
(

let uu____12842 = (sizeof arg)
in (acc + uu____12842))
end)) (Prims.parse_int "0") args)
in (uu____12823 + uu____12824)))
end
| uu____12843 -> begin
(Prims.parse_int "1")
end))


let is_fvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun lid t -> (

let uu____12854 = (

let uu____12855 = (un_uinst t)
in uu____12855.FStar_Syntax_Syntax.n)
in (match (uu____12854) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv lid)
end
| uu____12859 -> begin
false
end)))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (is_fvar FStar_Parser_Const.synth_lid t))


let has_attribute : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Ident.lident  ->  Prims.bool = (fun attrs attr -> (FStar_Util.for_some (is_fvar attr) attrs))


let process_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Range.range  ->  unit = (fun p r -> (

let set_options1 = (fun t s -> (

let uu____12900 = (FStar_Options.set_options t s)
in (match (uu____12900) with
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
| uu____12902 -> begin
()
end)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(set_options1 FStar_Options.Set o)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____12908 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____12908 (fun a237 -> ())));
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
| FStar_Syntax_Syntax.Tm_delayed (uu____12934) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uvar (uu____12962) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(x)::[]
end
| FStar_Syntax_Syntax.Tm_fvar (uu____12965) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (uu____12966) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_lazy (uu____12967) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
[]
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(unbound_variables t1)
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____12976) -> begin
(

let uu____12997 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____12997) with
| (bs1, t2) -> begin
(

let uu____13006 = (FStar_List.collect (fun uu____13016 -> (match (uu____13016) with
| (b, uu____13024) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____13025 = (unbound_variables t2)
in (FStar_List.append uu____13006 uu____13025)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____13046 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____13046) with
| (bs1, c1) -> begin
(

let uu____13055 = (FStar_List.collect (fun uu____13065 -> (match (uu____13065) with
| (b, uu____13073) -> begin
(unbound_variables b.FStar_Syntax_Syntax.sort)
end)) bs1)
in (

let uu____13074 = (unbound_variables_comp c1)
in (FStar_List.append uu____13055 uu____13074)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (b, t1) -> begin
(

let uu____13083 = (FStar_Syntax_Subst.open_term ((((b), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____13083) with
| (bs, t2) -> begin
(

let uu____13100 = (FStar_List.collect (fun uu____13110 -> (match (uu____13110) with
| (b1, uu____13118) -> begin
(unbound_variables b1.FStar_Syntax_Syntax.sort)
end)) bs)
in (

let uu____13119 = (unbound_variables t2)
in (FStar_List.append uu____13100 uu____13119)))
end))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____13144 = (FStar_List.collect (fun uu____13156 -> (match (uu____13156) with
| (x, uu____13166) -> begin
(unbound_variables x)
end)) args)
in (

let uu____13171 = (unbound_variables t1)
in (FStar_List.append uu____13144 uu____13171)))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____13212 = (unbound_variables t1)
in (

let uu____13215 = (FStar_All.pipe_right pats (FStar_List.collect (fun br -> (

let uu____13230 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____13230) with
| (p, wopt, t2) -> begin
(

let uu____13252 = (unbound_variables t2)
in (

let uu____13255 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t3) -> begin
(unbound_variables t3)
end)
in (FStar_List.append uu____13252 uu____13255)))
end)))))
in (FStar_List.append uu____13212 uu____13215)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____13269) -> begin
(

let uu____13310 = (unbound_variables t1)
in (

let uu____13313 = (

let uu____13316 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(unbound_variables t2)
end
| FStar_Util.Inr (c2) -> begin
(unbound_variables_comp c2)
end)
in (

let uu____13347 = (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (tac) -> begin
(unbound_variables tac)
end)
in (FStar_List.append uu____13316 uu____13347)))
in (FStar_List.append uu____13310 uu____13313)))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t1) -> begin
(

let uu____13385 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____13388 = (

let uu____13391 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____13394 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____13399) -> begin
(unbound_variables t1)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____13401 = (FStar_Syntax_Subst.open_term ((((bv), (FStar_Pervasives_Native.None)))::[]) t1)
in (match (uu____13401) with
| (uu____13416, t2) -> begin
(unbound_variables t2)
end))
end)
in (FStar_List.append uu____13391 uu____13394)))
in (FStar_List.append uu____13385 uu____13388)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____13418, lbs), t1) -> begin
(

let uu____13435 = (FStar_Syntax_Subst.open_let_rec lbs t1)
in (match (uu____13435) with
| (lbs1, t2) -> begin
(

let uu____13450 = (unbound_variables t2)
in (

let uu____13453 = (FStar_List.collect (fun lb -> (

let uu____13460 = (unbound_variables lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____13463 = (unbound_variables lb.FStar_Syntax_Syntax.lbdef)
in (FStar_List.append uu____13460 uu____13463)))) lbs1)
in (FStar_List.append uu____13450 uu____13453)))
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

let uu____13480 = (unbound_variables t1)
in (

let uu____13483 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_List.collect (FStar_List.collect (fun uu____13516 -> (match (uu____13516) with
| (a, uu____13526) -> begin
(unbound_variables a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____13531, uu____13532, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____13538, t') -> begin
(unbound_variables t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____13544) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_desugared (uu____13551) -> begin
[]
end
| FStar_Syntax_Syntax.Meta_named (uu____13552) -> begin
[]
end)
in (FStar_List.append uu____13480 uu____13483)))
end)))
and unbound_variables_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____13559) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Total (t, uu____13569) -> begin
(unbound_variables t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____13579 = (unbound_variables ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____13582 = (FStar_List.collect (fun uu____13594 -> (match (uu____13594) with
| (a, uu____13604) -> begin
(unbound_variables a)
end)) ct.FStar_Syntax_Syntax.effect_args)
in (FStar_List.append uu____13579 uu____13582)))
end))




