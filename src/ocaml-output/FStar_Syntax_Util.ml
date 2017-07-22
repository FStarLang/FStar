
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
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____2018 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2018))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2031 = (eq_tm f g)
in (eq_and uu____2031 (fun uu____2034 -> (

let uu____2035 = (eq_univs_list us vs)
in (equal_if uu____2035)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2038 = (FStar_Const.eq_const c d)
in (equal_iff uu____2038))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____2040), FStar_Syntax_Syntax.Tm_uvar (u2, uu____2042)) -> begin
(

let uu____2091 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (equal_if uu____2091))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2136 = (

let uu____2141 = (

let uu____2142 = (un_uinst h1)
in uu____2142.FStar_Syntax_Syntax.n)
in (

let uu____2145 = (

let uu____2146 = (un_uinst h2)
in uu____2146.FStar_Syntax_Syntax.n)
in ((uu____2141), (uu____2145))))
in (match (uu____2136) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((f1.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) && (f2.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) -> begin
(

let uu____2155 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2155) with
| true -> begin
(

let uu____2159 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2221 -> (match (uu____2221) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2249 = (eq_tm a1 a2)
in (eq_inj acc uu____2249))
end)) Equal) uu____2159))
end
| uu____2250 -> begin
NotEqual
end))
end
| uu____2251 -> begin
(

let uu____2256 = (eq_tm h1 h2)
in (eq_and uu____2256 (fun uu____2258 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____2261 = (eq_univs u v1)
in (equal_if uu____2261))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____2263), uu____2264) -> begin
(eq_tm t12 t21)
end
| (uu____2269, FStar_Syntax_Syntax.Tm_meta (t22, uu____2271)) -> begin
(eq_tm t11 t22)
end
| uu____2276 -> begin
Unknown
end)))))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____2312))::a11, ((b, uu____2315))::b1) -> begin
(

let uu____2369 = (eq_tm a b)
in (match (uu____2369) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____2370 -> begin
Unknown
end))
end
| uu____2371 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2384) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2390, uu____2391) -> begin
(unrefine t2)
end
| uu____2432 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2437 = (

let uu____2438 = (unrefine t)
in uu____2438.FStar_Syntax_Syntax.n)
in (match (uu____2437) with
| FStar_Syntax_Syntax.Tm_type (uu____2441) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2444) -> begin
(is_unit t1)
end
| uu____2449 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2454 = (

let uu____2455 = (unrefine t)
in uu____2455.FStar_Syntax_Syntax.n)
in (match (uu____2454) with
| FStar_Syntax_Syntax.Tm_type (uu____2458) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____2461) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2483) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2488, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____2506 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____2511 = (

let uu____2512 = (FStar_Syntax_Subst.compress e)
in uu____2512.FStar_Syntax_Syntax.n)
in (match (uu____2511) with
| FStar_Syntax_Syntax.Tm_abs (uu____2515) -> begin
true
end
| uu____2532 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2537 = (

let uu____2538 = (FStar_Syntax_Subst.compress t)
in uu____2538.FStar_Syntax_Syntax.n)
in (match (uu____2537) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2541) -> begin
true
end
| uu____2554 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2561) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2567, uu____2568) -> begin
(pre_typ t2)
end
| uu____2609 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____2629 = (

let uu____2630 = (un_uinst typ1)
in uu____2630.FStar_Syntax_Syntax.n)
in (match (uu____2629) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____2685 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____2709 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____2726, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____2732, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2743, uu____2744, uu____2745, uu____2746, uu____2747) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____2757, uu____2758, uu____2759, uu____2760) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2766, uu____2767, uu____2768, uu____2769, uu____2770) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2776, uu____2777) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2779, uu____2780) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2783) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____2784) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____2785) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2797 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb : 'Auu____2816 'Auu____2817 . ((FStar_Syntax_Syntax.bv, FStar_Ident.lid) FStar_Util.either * 'Auu____2817 * 'Auu____2816)  ->  FStar_Range.range = (fun uu___164_2831 -> (match (uu___164_2831) with
| (FStar_Util.Inl (x), uu____2843, uu____2844) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____2850, uu____2851) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg : 'Auu____2862 'Auu____2863 . ('Auu____2863 FStar_Syntax_Syntax.syntax * 'Auu____2862)  ->  FStar_Range.range = (fun uu____2873 -> (match (uu____2873) with
| (hd1, uu____2881) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____2894 'Auu____2895 . ('Auu____2895 FStar_Syntax_Syntax.syntax * 'Auu____2894) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____3019 = (

let uu____3022 = (

let uu____3023 = (

let uu____3030 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3030), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____3023))
in (FStar_Syntax_Syntax.mk uu____3022))
in (uu____3019 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)))
end
| uu____3034 -> begin
(

let e = (

let uu____3046 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____3046 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____3059 = (

let uu____3064 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____3064), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3059))
end
| uu____3065 -> begin
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
| uu____3089 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____3107 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____3107) with
| true -> begin
(

let uu____3108 = (

let uu____3113 = (

let uu____3114 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____3114))
in (

let uu____3115 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____3113), (uu____3115))))
in (FStar_Ident.mk_ident uu____3108))
end
| uu____3116 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___168_3118 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___168_3118.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___168_3118.FStar_Syntax_Syntax.sort})
in (

let uu____3119 = (mk_field_projector_name_from_ident lid nm)
in ((uu____3119), (y))))))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uv t -> (

let uu____3128 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____3128) with
| FStar_Pervasives_Native.Some (uu____3131) -> begin
(

let uu____3132 = (

let uu____3133 = (

let uu____3134 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3134))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3133))
in (failwith uu____3132))
end
| uu____3135 -> begin
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
| uu____3208 -> begin
(q1 = q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3242 = (

let uu___169_3243 = rc
in (

let uu____3244 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___169_3243.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3244; FStar_Syntax_Syntax.residual_flags = uu___169_3243.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3242))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____3255 -> begin
(

let body = (

let uu____3257 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____3257))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____3285 = (

let uu____3288 = (

let uu____3289 = (

let uu____3306 = (

let uu____3313 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____3313 bs'))
in (

let uu____3324 = (close_lopt lopt')
in ((uu____3306), (t1), (uu____3324))))
in FStar_Syntax_Syntax.Tm_abs (uu____3289))
in (FStar_Syntax_Syntax.mk uu____3288))
in (uu____3285 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____3340 -> begin
(

let uu____3347 = (

let uu____3350 = (

let uu____3351 = (

let uu____3368 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3369 = (close_lopt lopt)
in ((uu____3368), (body), (uu____3369))))
in FStar_Syntax_Syntax.Tm_abs (uu____3351))
in (FStar_Syntax_Syntax.mk uu____3350))
in (uu____3347 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____3409 -> begin
(

let uu____3416 = (

let uu____3419 = (

let uu____3420 = (

let uu____3433 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3434 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____3433), (uu____3434))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3420))
in (FStar_Syntax_Syntax.mk uu____3419))
in (uu____3416 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____3467 = (

let uu____3468 = (FStar_Syntax_Subst.compress t)
in uu____3468.FStar_Syntax_Syntax.n)
in (match (uu____3467) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____3494) -> begin
(

let uu____3503 = (

let uu____3504 = (FStar_Syntax_Subst.compress tres)
in uu____3504.FStar_Syntax_Syntax.n)
in (match (uu____3503) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____3539 -> begin
t
end))
end
| uu____3540 -> begin
t
end)
end
| uu____3541 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____3552 = (

let uu____3553 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____3553 t.FStar_Syntax_Syntax.pos))
in (

let uu____3554 = (

let uu____3557 = (

let uu____3558 = (

let uu____3565 = (

let uu____3566 = (

let uu____3567 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____3567)::[])
in (FStar_Syntax_Subst.close uu____3566 t))
in ((b), (uu____3565)))
in FStar_Syntax_Syntax.Tm_refine (uu____3558))
in (FStar_Syntax_Syntax.mk uu____3557))
in (uu____3554 FStar_Pervasives_Native.None uu____3552))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3618 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3618) with
| (bs1, c1) -> begin
(

let uu____3635 = (is_tot_or_gtot_comp c1)
in (match (uu____3635) with
| true -> begin
(

let uu____3646 = (arrow_formals_comp (comp_result c1))
in (match (uu____3646) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____3691 -> begin
((bs1), (c1))
end))
end))
end
| uu____3692 -> begin
(

let uu____3693 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____3693)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____3720 = (arrow_formals_comp k)
in (match (uu____3720) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3797 = (

let uu___170_3798 = rc
in (

let uu____3799 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___170_3798.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3799; FStar_Syntax_Syntax.residual_flags = uu___170_3798.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3797))
end
| uu____3806 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____3834 = (

let uu____3835 = (

let uu____3838 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____3838))
in uu____3835.FStar_Syntax_Syntax.n)
in (match (uu____3834) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____3876 = (aux t2 what)
in (match (uu____3876) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____3936 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____3949 = (aux t FStar_Pervasives_Native.None)
in (match (uu____3949) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____3991 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____3991) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____4105) -> begin
def
end
| (uu____4116, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____4128) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_26 -> FStar_Syntax_Syntax.U_name (_0_26))))
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

let uu____4231 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____4231) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____4260 -> begin
(

let t' = (arrow binders c)
in (

let uu____4270 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____4270) with
| (uvs1, t'1) -> begin
(

let uu____4289 = (

let uu____4290 = (FStar_Syntax_Subst.compress t'1)
in uu____4290.FStar_Syntax_Syntax.n)
in (match (uu____4289) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____4331 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____4349 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4355 -> begin
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

let uu____4395 = (

let uu____4396 = (pre_typ t)
in uu____4396.FStar_Syntax_Syntax.n)
in (match (uu____4395) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____4400 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____4409 = (

let uu____4410 = (pre_typ t)
in uu____4410.FStar_Syntax_Syntax.n)
in (match (uu____4409) with
| FStar_Syntax_Syntax.Tm_fvar (uu____4413) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____4415) -> begin
(is_constructed_typ t1 lid)
end
| uu____4436 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____4446) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____4447) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4448) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____4450) -> begin
(get_tycon t2)
end
| uu____4471 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4483 = (

let uu____4484 = (un_uinst t)
in uu____4484.FStar_Syntax_Syntax.n)
in (match (uu____4483) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid)
end
| uu____4488 -> begin
false
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4493 = (

let uu____4494 = (un_uinst t)
in uu____4494.FStar_Syntax_Syntax.n)
in (match (uu____4493) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____4498 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____4510 -> (

let u = (

let uu____4516 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_27 -> FStar_Syntax_Syntax.U_unif (_0_27)) uu____4516))
in (

let uu____4533 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____4533), (u)))))


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

let uu____4585 = (

let uu____4588 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4589 = (

let uu____4592 = (

let uu____4593 = (

let uu____4608 = (

let uu____4611 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____4612 = (

let uu____4615 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4615)::[])
in (uu____4611)::uu____4612))
in ((tand), (uu____4608)))
in FStar_Syntax_Syntax.Tm_app (uu____4593))
in (FStar_Syntax_Syntax.mk uu____4592))
in (uu____4589 FStar_Pervasives_Native.None uu____4588)))
in FStar_Pervasives_Native.Some (uu____4585))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____4641 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4642 = (

let uu____4645 = (

let uu____4646 = (

let uu____4661 = (

let uu____4664 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____4665 = (

let uu____4668 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4668)::[])
in (uu____4664)::uu____4665))
in ((op_t), (uu____4661)))
in FStar_Syntax_Syntax.Tm_app (uu____4646))
in (FStar_Syntax_Syntax.mk uu____4645))
in (uu____4642 FStar_Pervasives_Native.None uu____4641))))


let mk_neg : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____4682 = (

let uu____4685 = (

let uu____4686 = (

let uu____4701 = (

let uu____4704 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____4704)::[])
in ((t_not), (uu____4701)))
in FStar_Syntax_Syntax.Tm_app (uu____4686))
in (FStar_Syntax_Syntax.mk uu____4685))
in (uu____4682 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


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

let uu____4776 = (

let uu____4779 = (

let uu____4780 = (

let uu____4795 = (

let uu____4798 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4798)::[])
in ((b2t_v), (uu____4795)))
in FStar_Syntax_Syntax.Tm_app (uu____4780))
in (FStar_Syntax_Syntax.mk uu____4779))
in (uu____4776 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____4814 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____4815 = (

let uu____4818 = (

let uu____4819 = (

let uu____4834 = (

let uu____4837 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____4838 = (

let uu____4841 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____4841)::[])
in (uu____4837)::uu____4838))
in ((teq), (uu____4834)))
in FStar_Syntax_Syntax.Tm_app (uu____4819))
in (FStar_Syntax_Syntax.mk uu____4818))
in (uu____4815 FStar_Pervasives_Native.None uu____4814))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____4864 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____4865 = (

let uu____4868 = (

let uu____4869 = (

let uu____4884 = (

let uu____4887 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____4888 = (

let uu____4891 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____4892 = (

let uu____4895 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____4895)::[])
in (uu____4891)::uu____4892))
in (uu____4887)::uu____4888))
in ((eq_inst), (uu____4884)))
in FStar_Syntax_Syntax.Tm_app (uu____4869))
in (FStar_Syntax_Syntax.mk uu____4868))
in (uu____4865 FStar_Pervasives_Native.None uu____4864)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____4921 = (

let uu____4924 = (

let uu____4925 = (

let uu____4940 = (

let uu____4943 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____4944 = (

let uu____4947 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____4948 = (

let uu____4951 = (FStar_Syntax_Syntax.as_arg t')
in (uu____4951)::[])
in (uu____4947)::uu____4948))
in (uu____4943)::uu____4944))
in ((t_has_type1), (uu____4940)))
in FStar_Syntax_Syntax.Tm_app (uu____4925))
in (FStar_Syntax_Syntax.mk uu____4924))
in (uu____4921 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____4961 = (

let uu____4964 = (

let uu____4965 = (

let uu____4972 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____4972), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4965))
in (FStar_Syntax_Syntax.mk uu____4964))
in (uu____4961 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____4986 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____4999) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____5010) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____4986) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____5031 -> c0)}
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____5096 = (

let uu____5099 = (

let uu____5100 = (

let uu____5115 = (

let uu____5118 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____5119 = (

let uu____5122 = (

let uu____5123 = (

let uu____5124 = (

let uu____5125 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5125)::[])
in (abs uu____5124 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____5123))
in (uu____5122)::[])
in (uu____5118)::uu____5119))
in ((fa), (uu____5115)))
in FStar_Syntax_Syntax.Tm_app (uu____5100))
in (FStar_Syntax_Syntax.mk uu____5099))
in (uu____5096 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____5171 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____5171) with
| true -> begin
f1
end
| uu____5172 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____5181) -> begin
true
end
| uu____5182 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____5224 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____5224), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____5252 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____5252), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____5265 = (

let uu____5266 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5266))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____5265)))))


let mk_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____5334 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____5337 = (

let uu____5346 = (FStar_Syntax_Syntax.as_arg p)
in (uu____5346)::[])
in (mk_app uu____5334 uu____5337)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____5355 = (head_and_args t)
in (match (uu____5355) with
| (head1, args) -> begin
(

let uu____5396 = (

let uu____5409 = (

let uu____5410 = (un_uinst head1)
in uu____5410.FStar_Syntax_Syntax.n)
in ((uu____5409), (args)))
in (match (uu____5396) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____5427))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____5479 = (

let uu____5484 = (

let uu____5485 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____5485)::[])
in (FStar_Syntax_Subst.open_term uu____5484 p))
in (match (uu____5479) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5514 -> begin
(failwith "impossible")
end)
in (

let uu____5519 = (

let uu____5520 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____5520))
in (match (uu____5519) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5529 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____5530 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5533 -> begin
FStar_Pervasives_Native.None
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____5564 = (

let uu____5565 = (FStar_Syntax_Subst.compress t)
in uu____5565.FStar_Syntax_Syntax.n)
in (match (uu____5564) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____5662 = (

let uu____5671 = (

let uu____5672 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____5672))
in ((b), (uu____5671)))
in FStar_Pervasives_Native.Some (uu____5662))
end
| uu____5685 -> begin
FStar_Pervasives_Native.None
end)))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5698 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5698)))


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
| uu____5742 -> begin
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
| uu____5780 -> begin
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
| uu____5816 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____5851)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____5863)) -> begin
(unmeta_monadic t)
end
| uu____5876 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____5954 -> (match (uu____5954) with
| (lid, arity) -> begin
(

let uu____5963 = (

let uu____5978 = (unmeta_monadic f2)
in (head_and_args uu____5978))
in (match (uu____5963) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____6004 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____6004) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____6025 -> begin
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

let uu____6079 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____6079)))
end
| uu____6090 -> begin
(

let uu____6091 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____6091)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____6123 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____6138 = (head_and_args t1)
in (match (uu____6138) with
| (t2, args) -> begin
(

let uu____6185 = (un_uinst t2)
in (

let uu____6186 = (FStar_All.pipe_right args (FStar_List.map (fun uu____6219 -> (match (uu____6219) with
| (t3, imp) -> begin
(

let uu____6230 = (unascribe t3)
in ((uu____6230), (imp)))
end))))
in ((uu____6185), (uu____6186))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____6265 = (

let uu____6282 = (flat t1)
in ((qopt), (uu____6282)))
in (match (uu____6265) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6309; FStar_Syntax_Syntax.vars = uu____6310}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6313); FStar_Syntax_Syntax.pos = uu____6314; FStar_Syntax_Syntax.vars = uu____6315}, uu____6316))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6393; FStar_Syntax_Syntax.vars = uu____6394}, (uu____6395)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6398); FStar_Syntax_Syntax.pos = uu____6399; FStar_Syntax_Syntax.vars = uu____6400}, uu____6401))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6489; FStar_Syntax_Syntax.vars = uu____6490}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6493); FStar_Syntax_Syntax.pos = uu____6494; FStar_Syntax_Syntax.vars = uu____6495}, uu____6496))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6572; FStar_Syntax_Syntax.vars = uu____6573}, (uu____6574)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6577); FStar_Syntax_Syntax.pos = uu____6578; FStar_Syntax_Syntax.vars = uu____6579}, uu____6580))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (b), uu____6668) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____6702 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____6702) with
| (bs1, t2) -> begin
(

let uu____6711 = (patterns t2)
in (match (uu____6711) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____6762 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____6773 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____6839 = (un_squash t)
in (FStar_Util.bind_opt uu____6839 (fun t1 -> (

let uu____6855 = (head_and_args' t1)
in (match (uu____6855) with
| (hd1, args) -> begin
(

let uu____6888 = (

let uu____6893 = (

let uu____6894 = (un_uinst hd1)
in uu____6894.FStar_Syntax_Syntax.n)
in ((uu____6893), ((FStar_List.length args))))
in (match (uu____6888) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_28) when ((_0_28 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_and_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.and_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_29) when ((_0_29 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_or_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.or_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_30) when ((_0_30 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_31) when ((_0_31 = (Prims.parse_int "3")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_32) when ((_0_32 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_33) when ((_0_33 = (Prims.parse_int "4")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_34) when ((_0_34 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_true_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.true_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_35) when ((_0_35 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_false_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.false_lid), (args))))
end
| uu____6977 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____7000 = (un_squash t)
in (FStar_Util.bind_opt uu____7000 (fun t1 -> (

let uu____7015 = (arrow_one t1)
in (match (uu____7015) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____7030 = (

let uu____7031 = (is_tot_or_gtot_comp c)
in (not (uu____7031)))
in (match (uu____7030) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7034 -> begin
(

let q = (

let uu____7038 = (comp_to_comp_typ c)
in uu____7038.FStar_Syntax_Syntax.result_typ)
in (

let uu____7039 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7039) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7070 -> begin
(failwith "impossible")
end)
in (

let uu____7075 = (is_free_in (FStar_Pervasives_Native.fst b1) q1)
in (match (uu____7075) with
| true -> begin
(

let uu____7078 = (patterns q1)
in (match (uu____7078) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b1)::[]), (pats), (q2))))))
end))
end
| uu____7145 -> begin
(

let uu____7146 = (

let uu____7147 = (

let uu____7152 = (

let uu____7155 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort)
in (

let uu____7156 = (

let uu____7159 = (FStar_Syntax_Syntax.as_arg q1)
in (uu____7159)::[])
in (uu____7155)::uu____7156))
in ((FStar_Parser_Const.imp_lid), (uu____7152)))
in BaseConn (uu____7147))
in FStar_Pervasives_Native.Some (uu____7146))
end)))
end)))
end))
end
| uu____7162 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____7170 = (un_squash t)
in (FStar_Util.bind_opt uu____7170 (fun t1 -> (

let uu____7201 = (head_and_args' t1)
in (match (uu____7201) with
| (hd1, args) -> begin
(

let uu____7234 = (

let uu____7247 = (

let uu____7248 = (un_uinst hd1)
in uu____7248.FStar_Syntax_Syntax.n)
in ((uu____7247), (args)))
in (match (uu____7234) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____7263))::((a2, uu____7265))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____7300 = (

let uu____7301 = (FStar_Syntax_Subst.compress a2)
in uu____7301.FStar_Syntax_Syntax.n)
in (match (uu____7300) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____7308) -> begin
(

let uu____7335 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7335) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7374 -> begin
(failwith "impossible")
end)
in (

let uu____7379 = (patterns q1)
in (match (uu____7379) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____7446 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7447 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____7468 = (destruct_sq_forall phi)
in (match (uu____7468) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_36 -> FStar_Pervasives_Native.Some (_0_36)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7490 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____7496 = (destruct_sq_exists phi)
in (match (uu____7496) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7518 -> begin
f1
end))
end
| uu____7521 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____7525 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____7525 (fun uu____7530 -> (

let uu____7531 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____7531 (fun uu____7536 -> (

let uu____7537 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____7537 (fun uu____7542 -> (

let uu____7543 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____7543 (fun uu____7548 -> (

let uu____7549 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____7549 (fun uu____7553 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____7563 = (

let uu____7568 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7568))
in (

let uu____7569 = (

let uu____7570 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____7570))
in (

let uu____7573 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____7563 a.FStar_Syntax_Syntax.action_univs uu____7569 FStar_Parser_Const.effect_Tot_lid uu____7573))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____7599 = (

let uu____7602 = (

let uu____7603 = (

let uu____7618 = (

let uu____7621 = (FStar_Syntax_Syntax.as_arg t)
in (uu____7621)::[])
in ((reify_), (uu____7618)))
in FStar_Syntax_Syntax.Tm_app (uu____7603))
in (FStar_Syntax_Syntax.mk uu____7602))
in (uu____7599 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____7634) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____7660) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____7661) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____7662) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7685) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____7702) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____7703) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7704) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____7718) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____7723; FStar_Syntax_Syntax.index = uu____7724; FStar_Syntax_Syntax.sort = t2}, uu____7726) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____7734) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7740, uu____7741) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____7783) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____7804, t2, uu____7806) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____7827, t2) -> begin
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

let uu____7855 = (delta_qualifier t)
in (incr_delta_depth uu____7855)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7860 = (

let uu____7861 = (FStar_Syntax_Subst.compress t)
in uu____7861.FStar_Syntax_Syntax.n)
in (match (uu____7860) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____7864 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____7877 = (

let uu____7892 = (unmeta e)
in (head_and_args uu____7892))
in (match (uu____7877) with
| (head1, args) -> begin
(

let uu____7919 = (

let uu____7932 = (

let uu____7933 = (un_uinst head1)
in uu____7933.FStar_Syntax_Syntax.n)
in ((uu____7932), (args)))
in (match (uu____7919) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____7949) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7969)::((hd1, uu____7971))::((tl1, uu____7973))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____8020 = (

let uu____8025 = (

let uu____8030 = (list_elements tl1)
in (FStar_Util.must uu____8030))
in (hd1)::uu____8025)
in FStar_Pervasives_Native.Some (uu____8020))
end
| uu____8043 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____8064 . ('Auu____8064  ->  'Auu____8064)  ->  'Auu____8064 Prims.list  ->  'Auu____8064 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____8087 = (f a)
in (uu____8087)::[])
end
| (x)::xs -> begin
(

let uu____8092 = (apply_last f xs)
in (x)::uu____8092)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____8133 = (

let uu____8136 = (

let uu____8137 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____8137))
in (FStar_Syntax_Syntax.mk uu____8136))
in (uu____8133 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____8150 = (

let uu____8151 = (

let uu____8152 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8152 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8151 args))
in (uu____8150 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____8164 = (

let uu____8165 = (

let uu____8166 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8166 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8165 args))
in (uu____8164 FStar_Pervasives_Native.None pos)))
in (

let uu____8169 = (

let uu____8170 = (

let uu____8171 = (FStar_Syntax_Syntax.iarg typ)
in (uu____8171)::[])
in (nil uu____8170 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____8177 = (

let uu____8178 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____8179 = (

let uu____8182 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8183 = (

let uu____8186 = (FStar_Syntax_Syntax.as_arg a)
in (uu____8186)::[])
in (uu____8182)::uu____8183))
in (uu____8178)::uu____8179))
in (cons1 uu____8177 t.FStar_Syntax_Syntax.pos))) l uu____8169))))))


let uvar_from_id : Prims.int  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id t -> (

let uu____8197 = (

let uu____8200 = (

let uu____8201 = (

let uu____8218 = (FStar_Syntax_Unionfind.from_id id)
in ((uu____8218), (t)))
in FStar_Syntax_Syntax.Tm_uvar (uu____8201))
in (FStar_Syntax_Syntax.mk uu____8200))
in (uu____8197 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____8281 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____8384 -> begin
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
| uu____8532 -> begin
false
end))


let rec term_eq : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun t1 t2 -> (

let canon_app = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____8651) -> begin
(

let uu____8666 = (head_and_args' t)
in (match (uu____8666) with
| (hd1, args) -> begin
(

let uu___171_8699 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args))); FStar_Syntax_Syntax.pos = uu___171_8699.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___171_8699.FStar_Syntax_Syntax.vars})
end))
end
| uu____8710 -> begin
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
| (uu____8981, uu____8982) -> begin
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
| (uu____9079, uu____9080) -> begin
false
end))
and eq_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  Prims.bool = (fun f1 f2 -> false)
and branch_eq : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun uu____9087 uu____9088 -> (match (((uu____9087), (uu____9088))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
false
end))


let rec bottom_fold : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun f t -> (

let ff = (bottom_fold f)
in (

let tn = (

let uu____9228 = (FStar_Syntax_Subst.compress t)
in uu____9228.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (f1, args) -> begin
(

let uu____9254 = (

let uu____9269 = (ff f1)
in (

let uu____9270 = (FStar_List.map (fun uu____9289 -> (match (uu____9289) with
| (a, q) -> begin
(

let uu____9300 = (ff a)
in ((uu____9300), (q)))
end)) args)
in ((uu____9269), (uu____9270))))
in FStar_Syntax_Syntax.Tm_app (uu____9254))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____9330 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____9330) with
| (bs1, t') -> begin
(

let t'' = (ff t')
in (

let uu____9338 = (

let uu____9355 = (FStar_Syntax_Subst.close bs1 t'')
in ((bs1), (uu____9355), (k)))
in FStar_Syntax_Syntax.Tm_abs (uu____9338)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
tn
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9382 = (

let uu____9389 = (ff t1)
in ((uu____9389), (us)))
in FStar_Syntax_Syntax.Tm_uinst (uu____9382))
end
| uu____9390 -> begin
tn
end)
in (f (

let uu___172_9393 = t
in {FStar_Syntax_Syntax.n = tn1; FStar_Syntax_Syntax.pos = uu___172_9393.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___172_9393.FStar_Syntax_Syntax.vars}))))))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9398) -> begin
(

let uu____9423 = (

let uu____9424 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____9424))
in ((Prims.parse_int "1") + uu____9423))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____9426 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9426))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____9428 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9428))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9435 = (sizeof t1)
in ((FStar_List.length us) + uu____9435))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____9438) -> begin
(

let uu____9459 = (sizeof t1)
in (

let uu____9460 = (FStar_List.fold_left (fun acc uu____9471 -> (match (uu____9471) with
| (bv, uu____9477) -> begin
(

let uu____9478 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____9478))
end)) (Prims.parse_int "0") bs)
in (uu____9459 + uu____9460)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9501 = (sizeof hd1)
in (

let uu____9502 = (FStar_List.fold_left (fun acc uu____9513 -> (match (uu____9513) with
| (arg, uu____9519) -> begin
(

let uu____9520 = (sizeof arg)
in (acc + uu____9520))
end)) (Prims.parse_int "0") args)
in (uu____9501 + uu____9502)))
end
| uu____9521 -> begin
(Prims.parse_int "1")
end))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9526 = (

let uu____9527 = (un_uinst t)
in uu____9527.FStar_Syntax_Syntax.n)
in (match (uu____9526) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid)
end
| uu____9531 -> begin
false
end)))


let mk_alien : 'a . 'a  ->  Prims.string  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun b s r -> (

let uu____9557 = (

let uu____9560 = (

let uu____9561 = (

let uu____9568 = (

let uu____9569 = (

let uu____9574 = (FStar_Dyn.mkdyn b)
in ((uu____9574), (s)))
in FStar_Syntax_Syntax.Meta_alien (uu____9569))
in ((FStar_Syntax_Syntax.tun), (uu____9568)))
in FStar_Syntax_Syntax.Tm_meta (uu____9561))
in (FStar_Syntax_Syntax.mk uu____9560))
in (uu____9557 FStar_Pervasives_Native.None (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
r1
end
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end))))


let un_alien : FStar_Syntax_Syntax.term  ->  FStar_Dyn.dyn = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____9586, FStar_Syntax_Syntax.Meta_alien (blob, uu____9588)) -> begin
blob
end
| uu____9593 -> begin
(failwith "Something paranormal occurred")
end))




