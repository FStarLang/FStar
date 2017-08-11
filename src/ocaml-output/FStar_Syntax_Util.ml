
open Prims
open FStar_Pervasives

let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (

let uu____9 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____23 . (FStar_Syntax_Syntax.bv * 'Auu____23)  ->  (FStar_Syntax_Syntax.term * 'Auu____23) = (fun uu____35 -> (match (uu____35) with
| (b, imp) -> begin
(

let uu____42 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____42), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____66 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____66) with
| true -> begin
[]
end
| uu____77 -> begin
(

let uu____78 = (arg_of_non_null_binder b)
in (uu____78)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____103 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____149 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____149) with
| true -> begin
(

let b1 = (

let uu____167 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____167), ((FStar_Pervasives_Native.snd b))))
in (

let uu____168 = (arg_of_non_null_binder b1)
in ((b1), (uu____168))))
end
| uu____181 -> begin
(

let uu____182 = (arg_of_non_null_binder b)
in ((b), (uu____182)))
end)))))
in (FStar_All.pipe_right uu____103 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____265 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____265) with
| true -> begin
(

let uu____270 = b
in (match (uu____270) with
| (a, imp) -> begin
(

let b1 = (

let uu____278 = (

let uu____279 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____279))
in (FStar_Ident.id_of_text uu____278))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____281 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____312 = (

let uu____315 = (

let uu____316 = (

let uu____329 = (name_binders binders)
in ((uu____329), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____316))
in (FStar_Syntax_Syntax.mk uu____315))
in (uu____312 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____347 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____388 -> (match (uu____388) with
| (t, imp) -> begin
(

let uu____399 = (

let uu____400 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____400))
in ((uu____399), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____451 -> (match (uu____451) with
| (t, imp) -> begin
(

let uu____468 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____468), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____479 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____479 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____490 . 'Auu____490  ->  'Auu____490 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____549 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match (((FStar_List.length replace_xs) = (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____581 uu____582 -> (match (((uu____581), (uu____582))) with
| ((x, uu____600), (y, uu____602)) -> begin
(

let uu____611 = (

let uu____618 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____618)))
in FStar_Syntax_Syntax.NT (uu____611))
end)) replace_xs with_ys)
end
| uu____619 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____626) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____632, uu____633) -> begin
(unmeta e2)
end
| uu____674 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____687) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____688) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____698 = (univ_kernel u1)
in (match (uu____698) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____709) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____716) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____725 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____725)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____738), uu____739) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____740, FStar_Syntax_Syntax.U_bvar (uu____741)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____742) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____743, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____744) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____745, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____748), FStar_Syntax_Syntax.U_unif (uu____749)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____758), FStar_Syntax_Syntax.U_name (uu____759)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____786 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____787 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____786 - uu____787)))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in (match ((n1 <> n2)) with
| true -> begin
(n1 - n2)
end
| uu____814 -> begin
(

let copt = (

let uu____818 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____818 (fun uu____833 -> (match (uu____833) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((c <> (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____845 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____847), uu____848) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____851, FStar_Syntax_Syntax.U_max (uu____852)) -> begin
(Prims.parse_int "1")
end
| uu____855 -> begin
(

let uu____860 = (univ_kernel u1)
in (match (uu____860) with
| (k1, n1) -> begin
(

let uu____867 = (univ_kernel u2)
in (match (uu____867) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((r = (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____875 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____884 = (compare_univs u1 u2)
in (uu____884 = (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____912) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____921) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____942) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____951) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let comp_to_comp_typ = (fun c1 -> (match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c2) -> begin
c2
end
| FStar_Syntax_Syntax.Total (t, u_opt) -> begin
(

let uu____990 = (

let uu____991 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____991))
in {FStar_Syntax_Syntax.comp_univs = uu____990; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1018 = (

let uu____1019 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1019))
in {FStar_Syntax_Syntax.comp_univs = uu____1018; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end))
in (

let uu___165_1036 = c
in (

let uu____1037 = (

let uu____1038 = (

let uu___166_1039 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___166_1039.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___166_1039.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___166_1039.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___166_1039.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1038))
in {FStar_Syntax_Syntax.n = uu____1037; FStar_Syntax_Syntax.pos = uu___165_1036.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___165_1036.FStar_Syntax_Syntax.vars}))))


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
| uu____1073 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1083) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1092) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___153_1112 -> (match (uu___153_1112) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1113 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___154_1121 -> (match (uu___154_1121) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1122 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___155_1130 -> (match (uu___155_1130) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1131 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___156_1143 -> (match (uu___156_1143) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1144 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___157_1152 -> (match (uu___157_1152) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1153 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1174) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1183) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___158_1196 -> (match (uu___158_1196) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1197 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___159_1217 -> (match (uu___159_1217) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1218 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1227 = (

let uu____1228 = (FStar_Syntax_Subst.compress t)
in uu____1228.FStar_Syntax_Syntax.n)
in (match (uu____1227) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1231, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1249 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1259 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1264 = (

let uu____1265 = (FStar_Syntax_Subst.compress t)
in uu____1265.FStar_Syntax_Syntax.n)
in (match (uu____1264) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1268, c) -> begin
(is_lemma_comp c)
end
| uu____1286 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1352 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1418 = (head_and_args' head1)
in (match (uu____1418) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1475 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1496) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1501 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1506 = (

let uu____1507 = (FStar_Syntax_Subst.compress t)
in uu____1507.FStar_Syntax_Syntax.n)
in (match (uu____1506) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1510, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1532))::uu____1533 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1577 = (head_and_args pats')
in (match (uu____1577) with
| (head1, uu____1593) -> begin
(

let uu____1614 = (

let uu____1615 = (un_uinst head1)
in uu____1615.FStar_Syntax_Syntax.n)
in (match (uu____1614) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1619 -> begin
false
end))
end)))
end
| uu____1620 -> begin
false
end)
end
| uu____1629 -> begin
false
end)
end
| uu____1630 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___160_1643 -> (match (uu___160_1643) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1644 -> begin
false
end)))))
end
| uu____1645 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1659) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1669) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1691) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1700) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___167_1712 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___167_1712.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___167_1712.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___167_1712.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___167_1712.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___161_1724 -> (match (uu___161_1724) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1725 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____1743 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1750, uu____1751) -> begin
(unascribe e2)
end
| uu____1792 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1842, uu____1843) -> begin
(ascribe t' k)
end
| uu____1884 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))

type eq_result =
| Equal
| NotEqual
| Unknown


let uu___is_Equal : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equal -> begin
true
end
| uu____1909 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1914 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1919 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let canon_app = (fun t -> (

let uu____1940 = (

let uu____1953 = (unascribe t)
in (head_and_args' uu____1953))
in (match (uu____1940) with
| (hd1, args) -> begin
(FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end)))
in (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___162_1983 -> (match (uu___162_1983) with
| true -> begin
Equal
end
| uu____1984 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___163_1988 -> (match (uu___163_1988) with
| true -> begin
Equal
end
| uu____1989 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____2002 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____2010) -> begin
NotEqual
end
| (uu____2011, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____2012) -> begin
Unknown
end
| (uu____2013, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____2051 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2051) with
| true -> begin
(

let uu____2055 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2113 -> (match (uu____2113) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2141 = (eq_tm a1 a2)
in (eq_inj acc uu____2141))
end)) Equal) uu____2055))
end
| uu____2142 -> begin
NotEqual
end)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((f.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) && (g.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) with
| true -> begin
(equal_data f [] g [])
end
| uu____2159 -> begin
(

let uu____2160 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2160))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2173 = (eq_tm f g)
in (eq_and uu____2173 (fun uu____2176 -> (

let uu____2177 = (eq_univs_list us vs)
in (equal_if uu____2177)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2180 = (FStar_Const.eq_const c d)
in (equal_iff uu____2180))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____2182), FStar_Syntax_Syntax.Tm_uvar (u2, uu____2184)) -> begin
(

let uu____2233 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (equal_if uu____2233))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2278 = (

let uu____2283 = (

let uu____2284 = (un_uinst h1)
in uu____2284.FStar_Syntax_Syntax.n)
in (

let uu____2287 = (

let uu____2288 = (un_uinst h2)
in uu____2288.FStar_Syntax_Syntax.n)
in ((uu____2283), (uu____2287))))
in (match (uu____2278) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((f1.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) && (f2.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____2297 -> begin
(

let uu____2302 = (eq_tm h1 h2)
in (eq_and uu____2302 (fun uu____2304 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____2307 = (eq_univs u v1)
in (equal_if uu____2307))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____2309), uu____2310) -> begin
(eq_tm t12 t21)
end
| (uu____2315, FStar_Syntax_Syntax.Tm_meta (t22, uu____2317)) -> begin
(eq_tm t11 t22)
end
| uu____2322 -> begin
Unknown
end))))))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____2358))::a11, ((b, uu____2361))::b1) -> begin
(

let uu____2415 = (eq_tm a b)
in (match (uu____2415) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____2416 -> begin
Unknown
end))
end
| uu____2417 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2430) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2436, uu____2437) -> begin
(unrefine t2)
end
| uu____2478 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2483 = (

let uu____2484 = (unrefine t)
in uu____2484.FStar_Syntax_Syntax.n)
in (match (uu____2483) with
| FStar_Syntax_Syntax.Tm_type (uu____2487) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2490) -> begin
(is_unit t1)
end
| uu____2495 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2500 = (

let uu____2501 = (unrefine t)
in uu____2501.FStar_Syntax_Syntax.n)
in (match (uu____2500) with
| FStar_Syntax_Syntax.Tm_type (uu____2504) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____2507) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2529) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2534, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____2552 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____2557 = (

let uu____2558 = (FStar_Syntax_Subst.compress e)
in uu____2558.FStar_Syntax_Syntax.n)
in (match (uu____2557) with
| FStar_Syntax_Syntax.Tm_abs (uu____2561) -> begin
true
end
| uu____2578 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2583 = (

let uu____2584 = (FStar_Syntax_Subst.compress t)
in uu____2584.FStar_Syntax_Syntax.n)
in (match (uu____2583) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2587) -> begin
true
end
| uu____2600 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2607) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2613, uu____2614) -> begin
(pre_typ t2)
end
| uu____2655 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____2675 = (

let uu____2676 = (un_uinst typ1)
in uu____2676.FStar_Syntax_Syntax.n)
in (match (uu____2675) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____2731 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____2755 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____2772, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____2778, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2789, uu____2790, uu____2791, uu____2792, uu____2793) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____2803, uu____2804, uu____2805, uu____2806) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2812, uu____2813, uu____2814, uu____2815, uu____2816) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2822, uu____2823) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2825, uu____2826) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2829) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____2830) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____2831) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2843 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb : 'Auu____2862 'Auu____2863 . ((FStar_Syntax_Syntax.bv, FStar_Ident.lid) FStar_Util.either * 'Auu____2863 * 'Auu____2862)  ->  FStar_Range.range = (fun uu___164_2877 -> (match (uu___164_2877) with
| (FStar_Util.Inl (x), uu____2889, uu____2890) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____2896, uu____2897) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg : 'Auu____2908 'Auu____2909 . ('Auu____2909 FStar_Syntax_Syntax.syntax * 'Auu____2908)  ->  FStar_Range.range = (fun uu____2919 -> (match (uu____2919) with
| (hd1, uu____2927) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____2940 'Auu____2941 . ('Auu____2941 FStar_Syntax_Syntax.syntax * 'Auu____2940) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____3065 = (

let uu____3068 = (

let uu____3069 = (

let uu____3076 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3076), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____3069))
in (FStar_Syntax_Syntax.mk uu____3068))
in (uu____3065 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)))
end
| uu____3080 -> begin
(

let e = (

let uu____3092 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____3092 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____3105 = (

let uu____3110 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____3110), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3105))
end
| uu____3111 -> begin
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
| uu____3135 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____3153 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____3153) with
| true -> begin
(

let uu____3154 = (

let uu____3159 = (

let uu____3160 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____3160))
in (

let uu____3161 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____3159), (uu____3161))))
in (FStar_Ident.mk_ident uu____3154))
end
| uu____3162 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___168_3164 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___168_3164.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___168_3164.FStar_Syntax_Syntax.sort})
in (

let uu____3165 = (mk_field_projector_name_from_ident lid nm)
in ((uu____3165), (y))))))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uv t -> (

let uu____3174 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____3174) with
| FStar_Pervasives_Native.Some (uu____3177) -> begin
(

let uu____3178 = (

let uu____3179 = (

let uu____3180 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3180))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3179))
in (failwith uu____3178))
end
| uu____3181 -> begin
(FStar_Syntax_Unionfind.change uv t)
end)))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText))
end
| (FStar_Syntax_Syntax.RecordType (ns1, f1), FStar_Syntax_Syntax.RecordType (ns2, f2)) -> begin
(((((FStar_List.length ns1) = (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2)) && ((FStar_List.length f1) = (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2))
end
| (FStar_Syntax_Syntax.RecordConstructor (ns1, f1), FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) -> begin
(((((FStar_List.length ns1) = (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2)) && ((FStar_List.length f1) = (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2))
end
| uu____3254 -> begin
(q1 = q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3288 = (

let uu___169_3289 = rc
in (

let uu____3290 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___169_3289.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3290; FStar_Syntax_Syntax.residual_flags = uu___169_3289.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3288))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____3301 -> begin
(

let body = (

let uu____3303 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____3303))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____3331 = (

let uu____3334 = (

let uu____3335 = (

let uu____3352 = (

let uu____3359 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____3359 bs'))
in (

let uu____3370 = (close_lopt lopt')
in ((uu____3352), (t1), (uu____3370))))
in FStar_Syntax_Syntax.Tm_abs (uu____3335))
in (FStar_Syntax_Syntax.mk uu____3334))
in (uu____3331 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____3386 -> begin
(

let uu____3393 = (

let uu____3396 = (

let uu____3397 = (

let uu____3414 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3415 = (close_lopt lopt)
in ((uu____3414), (body), (uu____3415))))
in FStar_Syntax_Syntax.Tm_abs (uu____3397))
in (FStar_Syntax_Syntax.mk uu____3396))
in (uu____3393 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____3455 -> begin
(

let uu____3462 = (

let uu____3465 = (

let uu____3466 = (

let uu____3479 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3480 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____3479), (uu____3480))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3466))
in (FStar_Syntax_Syntax.mk uu____3465))
in (uu____3462 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____3513 = (

let uu____3514 = (FStar_Syntax_Subst.compress t)
in uu____3514.FStar_Syntax_Syntax.n)
in (match (uu____3513) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____3540) -> begin
(

let uu____3549 = (

let uu____3550 = (FStar_Syntax_Subst.compress tres)
in uu____3550.FStar_Syntax_Syntax.n)
in (match (uu____3549) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____3585 -> begin
t
end))
end
| uu____3586 -> begin
t
end)
end
| uu____3587 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____3598 = (

let uu____3599 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____3599 t.FStar_Syntax_Syntax.pos))
in (

let uu____3600 = (

let uu____3603 = (

let uu____3604 = (

let uu____3611 = (

let uu____3612 = (

let uu____3613 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____3613)::[])
in (FStar_Syntax_Subst.close uu____3612 t))
in ((b), (uu____3611)))
in FStar_Syntax_Syntax.Tm_refine (uu____3604))
in (FStar_Syntax_Syntax.mk uu____3603))
in (uu____3600 FStar_Pervasives_Native.None uu____3598))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3664 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3664) with
| (bs1, c1) -> begin
(

let uu____3681 = (is_tot_or_gtot_comp c1)
in (match (uu____3681) with
| true -> begin
(

let uu____3692 = (arrow_formals_comp (comp_result c1))
in (match (uu____3692) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____3737 -> begin
((bs1), (c1))
end))
end))
end
| uu____3738 -> begin
(

let uu____3739 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____3739)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____3766 = (arrow_formals_comp k)
in (match (uu____3766) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3843 = (

let uu___170_3844 = rc
in (

let uu____3845 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___170_3844.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3845; FStar_Syntax_Syntax.residual_flags = uu___170_3844.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3843))
end
| uu____3852 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____3880 = (

let uu____3881 = (

let uu____3884 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____3884))
in uu____3881.FStar_Syntax_Syntax.n)
in (match (uu____3880) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____3922 = (aux t2 what)
in (match (uu____3922) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____3982 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____3995 = (aux t FStar_Pervasives_Native.None)
in (match (uu____3995) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____4037 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____4037) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____4151) -> begin
def
end
| (uu____4162, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____4174) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let inst1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst1 def)))
end)
in (

let typ1 = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def2 = (FStar_Syntax_Subst.close_univ_vars univ_vars def1)
in (mk_letbinding lbname univ_vars typ1 eff def2)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____4277 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____4277) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____4306 -> begin
(

let t' = (arrow binders c)
in (

let uu____4316 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____4316) with
| (uvs1, t'1) -> begin
(

let uu____4335 = (

let uu____4336 = (FStar_Syntax_Subst.compress t'1)
in uu____4336.FStar_Syntax_Syntax.n)
in (match (uu____4335) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____4377 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____4395 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4401 -> begin
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

let uu____4441 = (

let uu____4442 = (pre_typ t)
in uu____4442.FStar_Syntax_Syntax.n)
in (match (uu____4441) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____4446 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____4455 = (

let uu____4456 = (pre_typ t)
in uu____4456.FStar_Syntax_Syntax.n)
in (match (uu____4455) with
| FStar_Syntax_Syntax.Tm_fvar (uu____4459) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____4461) -> begin
(is_constructed_typ t1 lid)
end
| uu____4482 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____4492) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____4493) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4494) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____4496) -> begin
(get_tycon t2)
end
| uu____4517 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4529 = (

let uu____4530 = (un_uinst t)
in uu____4530.FStar_Syntax_Syntax.n)
in (match (uu____4529) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid)
end
| uu____4534 -> begin
false
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4539 = (

let uu____4540 = (un_uinst t)
in uu____4540.FStar_Syntax_Syntax.n)
in (match (uu____4539) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____4544 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____4556 -> (

let u = (

let uu____4562 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_29 -> FStar_Syntax_Syntax.U_unif (_0_29)) uu____4562))
in (

let uu____4579 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____4579), (u)))))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____4586 = (

let uu____4589 = (

let uu____4590 = (

let uu____4591 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4591 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____4590))
in (FStar_Syntax_Syntax.mk uu____4589))
in (uu____4586 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ((((FStar_Util.unicode_of_string s)), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.bool_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.true_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.not_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____4642 = (

let uu____4645 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4646 = (

let uu____4649 = (

let uu____4650 = (

let uu____4665 = (

let uu____4668 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____4669 = (

let uu____4672 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4672)::[])
in (uu____4668)::uu____4669))
in ((tand), (uu____4665)))
in FStar_Syntax_Syntax.Tm_app (uu____4650))
in (FStar_Syntax_Syntax.mk uu____4649))
in (uu____4646 FStar_Pervasives_Native.None uu____4645)))
in FStar_Pervasives_Native.Some (uu____4642))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____4698 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4699 = (

let uu____4702 = (

let uu____4703 = (

let uu____4718 = (

let uu____4721 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____4722 = (

let uu____4725 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4725)::[])
in (uu____4721)::uu____4722))
in ((op_t), (uu____4718)))
in FStar_Syntax_Syntax.Tm_app (uu____4703))
in (FStar_Syntax_Syntax.mk uu____4702))
in (uu____4699 FStar_Pervasives_Native.None uu____4698))))


let mk_neg : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____4739 = (

let uu____4742 = (

let uu____4743 = (

let uu____4758 = (

let uu____4761 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____4761)::[])
in ((t_not), (uu____4758)))
in FStar_Syntax_Syntax.Tm_app (uu____4743))
in (FStar_Syntax_Syntax.mk uu____4742))
in (uu____4739 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
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


let b2t : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e -> (

let uu____4833 = (

let uu____4836 = (

let uu____4837 = (

let uu____4852 = (

let uu____4855 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4855)::[])
in ((b2t_v), (uu____4852)))
in FStar_Syntax_Syntax.Tm_app (uu____4837))
in (FStar_Syntax_Syntax.mk uu____4836))
in (uu____4833 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____4871 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____4872 = (

let uu____4875 = (

let uu____4876 = (

let uu____4891 = (

let uu____4894 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____4895 = (

let uu____4898 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____4898)::[])
in (uu____4894)::uu____4895))
in ((teq), (uu____4891)))
in FStar_Syntax_Syntax.Tm_app (uu____4876))
in (FStar_Syntax_Syntax.mk uu____4875))
in (uu____4872 FStar_Pervasives_Native.None uu____4871))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____4921 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____4922 = (

let uu____4925 = (

let uu____4926 = (

let uu____4941 = (

let uu____4944 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____4945 = (

let uu____4948 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____4949 = (

let uu____4952 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____4952)::[])
in (uu____4948)::uu____4949))
in (uu____4944)::uu____4945))
in ((eq_inst), (uu____4941)))
in FStar_Syntax_Syntax.Tm_app (uu____4926))
in (FStar_Syntax_Syntax.mk uu____4925))
in (uu____4922 FStar_Pervasives_Native.None uu____4921)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____4978 = (

let uu____4981 = (

let uu____4982 = (

let uu____4997 = (

let uu____5000 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____5001 = (

let uu____5004 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____5005 = (

let uu____5008 = (FStar_Syntax_Syntax.as_arg t')
in (uu____5008)::[])
in (uu____5004)::uu____5005))
in (uu____5000)::uu____5001))
in ((t_has_type1), (uu____4997)))
in FStar_Syntax_Syntax.Tm_app (uu____4982))
in (FStar_Syntax_Syntax.mk uu____4981))
in (uu____4978 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____5018 = (

let uu____5021 = (

let uu____5022 = (

let uu____5029 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____5029), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5022))
in (FStar_Syntax_Syntax.mk uu____5021))
in (uu____5018 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____5043 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____5056) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____5067) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____5043) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____5088 -> c0)}
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____5153 = (

let uu____5156 = (

let uu____5157 = (

let uu____5172 = (

let uu____5175 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____5176 = (

let uu____5179 = (

let uu____5180 = (

let uu____5181 = (

let uu____5182 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5182)::[])
in (abs uu____5181 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____5180))
in (uu____5179)::[])
in (uu____5175)::uu____5176))
in ((fa), (uu____5172)))
in FStar_Syntax_Syntax.Tm_app (uu____5157))
in (FStar_Syntax_Syntax.mk uu____5156))
in (uu____5153 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____5228 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____5228) with
| true -> begin
f1
end
| uu____5229 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____5238) -> begin
true
end
| uu____5239 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____5281 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____5281), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____5309 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____5309), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____5322 = (

let uu____5323 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5323))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____5322)))))


let mk_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____5391 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____5394 = (

let uu____5403 = (FStar_Syntax_Syntax.as_arg p)
in (uu____5403)::[])
in (mk_app uu____5391 uu____5394)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____5412 = (head_and_args t)
in (match (uu____5412) with
| (head1, args) -> begin
(

let uu____5453 = (

let uu____5466 = (

let uu____5467 = (un_uinst head1)
in uu____5467.FStar_Syntax_Syntax.n)
in ((uu____5466), (args)))
in (match (uu____5453) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____5484))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____5536 = (

let uu____5541 = (

let uu____5542 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____5542)::[])
in (FStar_Syntax_Subst.open_term uu____5541 p))
in (match (uu____5536) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5571 -> begin
(failwith "impossible")
end)
in (

let uu____5576 = (

let uu____5577 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____5577))
in (match (uu____5576) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5586 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____5587 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5590 -> begin
FStar_Pervasives_Native.None
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____5621 = (

let uu____5622 = (FStar_Syntax_Subst.compress t)
in uu____5622.FStar_Syntax_Syntax.n)
in (match (uu____5621) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____5719 = (

let uu____5728 = (

let uu____5729 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____5729))
in ((b), (uu____5728)))
in FStar_Pervasives_Native.Some (uu____5719))
end
| uu____5742 -> begin
FStar_Pervasives_Native.None
end)))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5755 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5755)))


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
| uu____5799 -> begin
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
| uu____5837 -> begin
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
| uu____5873 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____5908)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____5920)) -> begin
(unmeta_monadic t)
end
| uu____5933 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____6011 -> (match (uu____6011) with
| (lid, arity) -> begin
(

let uu____6020 = (

let uu____6035 = (unmeta_monadic f2)
in (head_and_args uu____6035))
in (match (uu____6020) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____6061 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____6061) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____6082 -> begin
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

let uu____6136 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____6136)))
end
| uu____6147 -> begin
(

let uu____6148 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____6148)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____6180 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____6195 = (head_and_args t1)
in (match (uu____6195) with
| (t2, args) -> begin
(

let uu____6242 = (un_uinst t2)
in (

let uu____6243 = (FStar_All.pipe_right args (FStar_List.map (fun uu____6276 -> (match (uu____6276) with
| (t3, imp) -> begin
(

let uu____6287 = (unascribe t3)
in ((uu____6287), (imp)))
end))))
in ((uu____6242), (uu____6243))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____6322 = (

let uu____6339 = (flat t1)
in ((qopt), (uu____6339)))
in (match (uu____6322) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6366; FStar_Syntax_Syntax.vars = uu____6367}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6370); FStar_Syntax_Syntax.pos = uu____6371; FStar_Syntax_Syntax.vars = uu____6372}, uu____6373))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6450; FStar_Syntax_Syntax.vars = uu____6451}, (uu____6452)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6455); FStar_Syntax_Syntax.pos = uu____6456; FStar_Syntax_Syntax.vars = uu____6457}, uu____6458))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6546; FStar_Syntax_Syntax.vars = uu____6547}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6550); FStar_Syntax_Syntax.pos = uu____6551; FStar_Syntax_Syntax.vars = uu____6552}, uu____6553))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6629; FStar_Syntax_Syntax.vars = uu____6630}, (uu____6631)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6634); FStar_Syntax_Syntax.pos = uu____6635; FStar_Syntax_Syntax.vars = uu____6636}, uu____6637))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (b), uu____6725) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____6759 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____6759) with
| (bs1, t2) -> begin
(

let uu____6768 = (patterns t2)
in (match (uu____6768) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____6819 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____6830 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____6896 = (un_squash t)
in (FStar_Util.bind_opt uu____6896 (fun t1 -> (

let uu____6912 = (head_and_args' t1)
in (match (uu____6912) with
| (hd1, args) -> begin
(

let uu____6945 = (

let uu____6950 = (

let uu____6951 = (un_uinst hd1)
in uu____6951.FStar_Syntax_Syntax.n)
in ((uu____6950), ((FStar_List.length args))))
in (match (uu____6945) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_30) when ((_0_30 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_and_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.and_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_31) when ((_0_31 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_or_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.or_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_32) when ((_0_32 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_33) when ((_0_33 = (Prims.parse_int "3")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_34) when ((_0_34 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_35) when ((_0_35 = (Prims.parse_int "4")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_36) when ((_0_36 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_true_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.true_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_37) when ((_0_37 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_false_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.false_lid), (args))))
end
| uu____7034 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____7057 = (un_squash t)
in (FStar_Util.bind_opt uu____7057 (fun t1 -> (

let uu____7072 = (arrow_one t1)
in (match (uu____7072) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____7087 = (

let uu____7088 = (is_tot_or_gtot_comp c)
in (not (uu____7088)))
in (match (uu____7087) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7091 -> begin
(

let q = (

let uu____7095 = (comp_to_comp_typ c)
in uu____7095.FStar_Syntax_Syntax.result_typ)
in (

let uu____7096 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7096) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7127 -> begin
(failwith "impossible")
end)
in (

let uu____7132 = (is_free_in (FStar_Pervasives_Native.fst b1) q1)
in (match (uu____7132) with
| true -> begin
(

let uu____7135 = (patterns q1)
in (match (uu____7135) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b1)::[]), (pats), (q2))))))
end))
end
| uu____7202 -> begin
(

let uu____7203 = (

let uu____7204 = (

let uu____7209 = (

let uu____7212 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort)
in (

let uu____7213 = (

let uu____7216 = (FStar_Syntax_Syntax.as_arg q1)
in (uu____7216)::[])
in (uu____7212)::uu____7213))
in ((FStar_Parser_Const.imp_lid), (uu____7209)))
in BaseConn (uu____7204))
in FStar_Pervasives_Native.Some (uu____7203))
end)))
end)))
end))
end
| uu____7219 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____7227 = (un_squash t)
in (FStar_Util.bind_opt uu____7227 (fun t1 -> (

let uu____7258 = (head_and_args' t1)
in (match (uu____7258) with
| (hd1, args) -> begin
(

let uu____7291 = (

let uu____7304 = (

let uu____7305 = (un_uinst hd1)
in uu____7305.FStar_Syntax_Syntax.n)
in ((uu____7304), (args)))
in (match (uu____7291) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____7320))::((a2, uu____7322))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____7357 = (

let uu____7358 = (FStar_Syntax_Subst.compress a2)
in uu____7358.FStar_Syntax_Syntax.n)
in (match (uu____7357) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____7365) -> begin
(

let uu____7392 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7392) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7431 -> begin
(failwith "impossible")
end)
in (

let uu____7436 = (patterns q1)
in (match (uu____7436) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____7503 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7504 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____7525 = (destruct_sq_forall phi)
in (match (uu____7525) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7547 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____7553 = (destruct_sq_exists phi)
in (match (uu____7553) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7575 -> begin
f1
end))
end
| uu____7578 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____7582 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____7582 (fun uu____7587 -> (

let uu____7588 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____7588 (fun uu____7593 -> (

let uu____7594 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____7594 (fun uu____7599 -> (

let uu____7600 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____7600 (fun uu____7605 -> (

let uu____7606 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____7606 (fun uu____7610 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____7620 = (

let uu____7625 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7625))
in (

let uu____7626 = (

let uu____7627 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____7627))
in (

let uu____7630 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____7620 a.FStar_Syntax_Syntax.action_univs uu____7626 FStar_Parser_Const.effect_Tot_lid uu____7630))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____7656 = (

let uu____7659 = (

let uu____7660 = (

let uu____7675 = (

let uu____7678 = (FStar_Syntax_Syntax.as_arg t)
in (uu____7678)::[])
in ((reify_), (uu____7675)))
in FStar_Syntax_Syntax.Tm_app (uu____7660))
in (FStar_Syntax_Syntax.mk uu____7659))
in (uu____7656 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____7691) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____7717) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____7718) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____7719) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7742) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____7759) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____7760) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7761) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____7775) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____7780; FStar_Syntax_Syntax.index = uu____7781; FStar_Syntax_Syntax.sort = t2}, uu____7783) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____7791) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7797, uu____7798) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____7840) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____7861, t2, uu____7863) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____7884, t2) -> begin
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

let uu____7912 = (delta_qualifier t)
in (incr_delta_depth uu____7912)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7917 = (

let uu____7918 = (FStar_Syntax_Subst.compress t)
in uu____7918.FStar_Syntax_Syntax.n)
in (match (uu____7917) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____7921 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____7934 = (

let uu____7949 = (unmeta e)
in (head_and_args uu____7949))
in (match (uu____7934) with
| (head1, args) -> begin
(

let uu____7976 = (

let uu____7989 = (

let uu____7990 = (un_uinst head1)
in uu____7990.FStar_Syntax_Syntax.n)
in ((uu____7989), (args)))
in (match (uu____7976) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____8006) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8026)::((hd1, uu____8028))::((tl1, uu____8030))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____8077 = (

let uu____8082 = (

let uu____8087 = (list_elements tl1)
in (FStar_Util.must uu____8087))
in (hd1)::uu____8082)
in FStar_Pervasives_Native.Some (uu____8077))
end
| uu____8100 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____8121 . ('Auu____8121  ->  'Auu____8121)  ->  'Auu____8121 Prims.list  ->  'Auu____8121 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____8144 = (f a)
in (uu____8144)::[])
end
| (x)::xs -> begin
(

let uu____8149 = (apply_last f xs)
in (x)::uu____8149)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____8190 = (

let uu____8193 = (

let uu____8194 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____8194))
in (FStar_Syntax_Syntax.mk uu____8193))
in (uu____8190 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____8207 = (

let uu____8208 = (

let uu____8209 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8209 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8208 args))
in (uu____8207 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____8221 = (

let uu____8222 = (

let uu____8223 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8223 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8222 args))
in (uu____8221 FStar_Pervasives_Native.None pos)))
in (

let uu____8226 = (

let uu____8227 = (

let uu____8228 = (FStar_Syntax_Syntax.iarg typ)
in (uu____8228)::[])
in (nil uu____8227 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____8234 = (

let uu____8235 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____8236 = (

let uu____8239 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8240 = (

let uu____8243 = (FStar_Syntax_Syntax.as_arg a)
in (uu____8243)::[])
in (uu____8239)::uu____8240))
in (uu____8235)::uu____8236))
in (cons1 uu____8234 t.FStar_Syntax_Syntax.pos))) l uu____8226))))))


let uvar_from_id : Prims.int  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id t -> (

let uu____8254 = (

let uu____8257 = (

let uu____8258 = (

let uu____8275 = (FStar_Syntax_Unionfind.from_id id)
in ((uu____8275), (t)))
in FStar_Syntax_Syntax.Tm_uvar (uu____8258))
in (FStar_Syntax_Syntax.mk uu____8257))
in (uu____8254 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____8338 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____8441 -> begin
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
| uu____8589 -> begin
false
end))


let rec term_eq : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun t1 t2 -> (

let canon_app = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____8708) -> begin
(

let uu____8723 = (head_and_args' t)
in (match (uu____8723) with
| (hd1, args) -> begin
(

let uu___171_8756 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args))); FStar_Syntax_Syntax.pos = uu___171_8756.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___171_8756.FStar_Syntax_Syntax.vars})
end))
end
| uu____8767 -> begin
t
end))
in (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_bvar (x), FStar_Syntax_Syntax.Tm_bvar (y)) -> begin
(x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_fvar (x), FStar_Syntax_Syntax.Tm_fvar (y)) -> begin
(FStar_Syntax_Syntax.fv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_uinst (t12, us1), FStar_Syntax_Syntax.Tm_uinst (t22, us2)) -> begin
((eqlist eq_univs us1 us2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_constant (x), FStar_Syntax_Syntax.Tm_constant (y)) -> begin
(x = y)
end
| (FStar_Syntax_Syntax.Tm_type (x), FStar_Syntax_Syntax.Tm_type (y)) -> begin
(x = y)
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((eqlist binder_eq b1 b2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((term_eq f1 f2) && (eqlist arg_eq a1 a2))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((eqlist binder_eq b1 b2) && (comp_eq c1 c2))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((term_eq t12 t22) && (eqlist branch_eq bs1 bs2))
end
| (uu____9038, uu____9039) -> begin
false
end)))))
and arg_eq : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun a1 a2 -> (eqprod term_eq (fun q1 q2 -> (q1 = q2)) a1 a2))
and binder_eq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun b1 b2 -> (eqprod (fun b11 b21 -> (term_eq b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)) (fun q1 q2 -> (q1 = q2)) b1 b2))
and lcomp_eq : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> false)
and residual_eq : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> false)
and comp_eq : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c1 c2 -> (match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Total (t1, u1), FStar_Syntax_Syntax.Total (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.GTotal (t1, u1), FStar_Syntax_Syntax.GTotal (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.Comp (c11), FStar_Syntax_Syntax.Comp (c21)) -> begin
(((((c11.FStar_Syntax_Syntax.comp_univs = c21.FStar_Syntax_Syntax.comp_univs) && (c11.FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name)) && (term_eq c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)) && (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args c21.FStar_Syntax_Syntax.effect_args)) && (eq_flags c11.FStar_Syntax_Syntax.flags c21.FStar_Syntax_Syntax.flags))
end
| (uu____9136, uu____9137) -> begin
false
end))
and eq_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  Prims.bool = (fun f1 f2 -> false)
and branch_eq : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun uu____9144 uu____9145 -> (match (((uu____9144), (uu____9145))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
false
end))


let rec bottom_fold : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun f t -> (

let ff = (bottom_fold f)
in (

let tn = (

let uu____9285 = (FStar_Syntax_Subst.compress t)
in uu____9285.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (f1, args) -> begin
(

let uu____9311 = (

let uu____9326 = (ff f1)
in (

let uu____9327 = (FStar_List.map (fun uu____9346 -> (match (uu____9346) with
| (a, q) -> begin
(

let uu____9357 = (ff a)
in ((uu____9357), (q)))
end)) args)
in ((uu____9326), (uu____9327))))
in FStar_Syntax_Syntax.Tm_app (uu____9311))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____9387 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____9387) with
| (bs1, t') -> begin
(

let t'' = (ff t')
in (

let uu____9395 = (

let uu____9412 = (FStar_Syntax_Subst.close bs1 t'')
in ((bs1), (uu____9412), (k)))
in FStar_Syntax_Syntax.Tm_abs (uu____9395)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
tn
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9439 = (

let uu____9446 = (ff t1)
in ((uu____9446), (us)))
in FStar_Syntax_Syntax.Tm_uinst (uu____9439))
end
| uu____9447 -> begin
tn
end)
in (f (

let uu___172_9450 = t
in {FStar_Syntax_Syntax.n = tn1; FStar_Syntax_Syntax.pos = uu___172_9450.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___172_9450.FStar_Syntax_Syntax.vars}))))))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9455) -> begin
(

let uu____9480 = (

let uu____9481 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____9481))
in ((Prims.parse_int "1") + uu____9480))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____9483 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9483))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____9485 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9485))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9492 = (sizeof t1)
in ((FStar_List.length us) + uu____9492))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____9495) -> begin
(

let uu____9516 = (sizeof t1)
in (

let uu____9517 = (FStar_List.fold_left (fun acc uu____9528 -> (match (uu____9528) with
| (bv, uu____9534) -> begin
(

let uu____9535 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____9535))
end)) (Prims.parse_int "0") bs)
in (uu____9516 + uu____9517)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9558 = (sizeof hd1)
in (

let uu____9559 = (FStar_List.fold_left (fun acc uu____9570 -> (match (uu____9570) with
| (arg, uu____9576) -> begin
(

let uu____9577 = (sizeof arg)
in (acc + uu____9577))
end)) (Prims.parse_int "0") args)
in (uu____9558 + uu____9559)))
end
| uu____9578 -> begin
(Prims.parse_int "1")
end))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9583 = (

let uu____9584 = (un_uinst t)
in uu____9584.FStar_Syntax_Syntax.n)
in (match (uu____9583) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid)
end
| uu____9588 -> begin
false
end)))


let mk_alien : 'a . 'a  ->  Prims.string  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun b s r -> (

let uu____9614 = (

let uu____9617 = (

let uu____9618 = (

let uu____9625 = (

let uu____9626 = (

let uu____9631 = (FStar_Dyn.mkdyn b)
in ((uu____9631), (s)))
in FStar_Syntax_Syntax.Meta_alien (uu____9626))
in ((FStar_Syntax_Syntax.tun), (uu____9625)))
in FStar_Syntax_Syntax.Tm_meta (uu____9618))
in (FStar_Syntax_Syntax.mk uu____9617))
in (uu____9614 FStar_Pervasives_Native.None (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
r1
end
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end))))


let un_alien : FStar_Syntax_Syntax.term  ->  FStar_Dyn.dyn = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____9643, FStar_Syntax_Syntax.Meta_alien (blob, uu____9645)) -> begin
blob
end
| uu____9650 -> begin
(failwith "unexpected: term was not an alien embedding")
end))




