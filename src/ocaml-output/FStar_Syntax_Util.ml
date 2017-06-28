
open Prims
open FStar_Pervasives

let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (

let uu____9 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder = (fun uu____31 -> (match (uu____31) with
| (b, imp) -> begin
(

let uu____36 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____36), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____52 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____52) with
| true -> begin
[]
end
| uu____58 -> begin
(

let uu____59 = (arg_of_non_null_binder b)
in (uu____59)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____74 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____100 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____100) with
| true -> begin
(

let b1 = (

let uu____110 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____110), ((FStar_Pervasives_Native.snd b))))
in (

let uu____111 = (arg_of_non_null_binder b1)
in ((b1), (uu____111))))
end
| uu____118 -> begin
(

let uu____119 = (arg_of_non_null_binder b)
in ((b), (uu____119)))
end)))))
in (FStar_All.pipe_right uu____74 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____168 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____168) with
| true -> begin
(

let uu____171 = b
in (match (uu____171) with
| (a, imp) -> begin
(

let b1 = (

let uu____177 = (

let uu____178 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____178))
in (FStar_Ident.id_of_text uu____177))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____180 -> begin
b
end))))))


let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____208 = (

let uu____211 = (

let uu____212 = (

let uu____220 = (name_binders binders)
in ((uu____220), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____212))
in (FStar_Syntax_Syntax.mk uu____211))
in (uu____208 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____237 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____262 -> (match (uu____262) with
| (t, imp) -> begin
(

let uu____269 = (

let uu____270 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____270))
in ((uu____269), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____301 -> (match (uu____301) with
| (t, imp) -> begin
(

let uu____314 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____314), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____322 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____322 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____382 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match (((FStar_List.length replace_xs) = (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____414 uu____415 -> (match (((uu____414), (uu____415))) with
| ((x, uu____425), (y, uu____427)) -> begin
(

let uu____432 = (

let uu____437 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____437)))
in FStar_Syntax_Syntax.NT (uu____432))
end)) replace_xs with_ys)
end
| uu____438 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____445) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____451, uu____452) -> begin
(unmeta e2)
end
| uu____481 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____490) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____491) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____497 = (univ_kernel u1)
in (match (uu____497) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____504) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____508) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____515 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____515)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____526), uu____527) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____528, FStar_Syntax_Syntax.U_bvar (uu____529)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____530) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____531, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____532) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____533, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____536), FStar_Syntax_Syntax.U_unif (uu____537)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____542), FStar_Syntax_Syntax.U_name (uu____543)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____558 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____559 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____558 - uu____559)))
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
| uu____588 -> begin
(

let copt = (

let uu____591 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____591 (fun uu____601 -> (match (uu____601) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((c <> (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____609 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____611), uu____612) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____614, FStar_Syntax_Syntax.U_max (uu____615)) -> begin
(Prims.parse_int "1")
end
| uu____617 -> begin
(

let uu____620 = (univ_kernel u1)
in (match (uu____620) with
| (k1, n1) -> begin
(

let uu____625 = (univ_kernel u2)
in (match (uu____625) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((r = (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____631 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____640 = (compare_univs u1 u2)
in (uu____640 = (Prims.parse_int "0"))))


let ml_comp : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____671) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____677) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____697) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____703) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun c f -> (

let comp_to_comp_typ = (fun c1 -> (match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c2) -> begin
c2
end
| FStar_Syntax_Syntax.Total (t, u_opt) -> begin
(

let uu____735 = (

let uu____736 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____736))
in {FStar_Syntax_Syntax.comp_univs = uu____735; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____755 = (

let uu____756 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____756))
in {FStar_Syntax_Syntax.comp_univs = uu____755; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end))
in (

let uu___165_767 = c
in (

let uu____768 = (

let uu____769 = (

let uu___166_770 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___166_770.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___166_770.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___166_770.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___166_770.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____769))
in {FStar_Syntax_Syntax.n = uu____768; FStar_Syntax_Syntax.tk = uu___165_767.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___165_767.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___165_767.FStar_Syntax_Syntax.vars}))))


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
| uu____802 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____817) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____823) -> begin
false
end))


let is_total_comp = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___153_844 -> (match (uu___153_844) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____845 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___154_852 -> (match (uu___154_852) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____853 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___155_860 -> (match (uu___155_860) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____861 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___156_877 -> (match (uu___156_877) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____878 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___157_885 -> (match (uu___157_885) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____886 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____917) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____923) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___158_932 -> (match (uu___158_932) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____933 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___159_957 -> (match (uu___159_957) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____958 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____967 = (

let uu____968 = (FStar_Syntax_Subst.compress t)
in uu____968.FStar_Syntax_Syntax.n)
in (match (uu____967) with
| FStar_Syntax_Syntax.Tm_arrow (uu____971, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____983 -> begin
true
end)))


let is_lemma_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____998 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1003 = (

let uu____1004 = (FStar_Syntax_Subst.compress t)
in uu____1004.FStar_Syntax_Syntax.n)
in (match (uu____1003) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1007, c) -> begin
(is_lemma_comp c)
end
| uu____1019 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1066 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1111 = (head_and_args' head1)
in (match (uu____1111) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1147 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1163) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1168 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1173 = (

let uu____1174 = (FStar_Syntax_Subst.compress t)
in uu____1174.FStar_Syntax_Syntax.n)
in (match (uu____1173) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1177, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1193))::uu____1194 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1225 = (head_and_args pats')
in (match (uu____1225) with
| (head1, uu____1236) -> begin
(

let uu____1251 = (

let uu____1252 = (un_uinst head1)
in uu____1252.FStar_Syntax_Syntax.n)
in (match (uu____1251) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1256 -> begin
false
end))
end)))
end
| uu____1257 -> begin
false
end)
end
| uu____1263 -> begin
false
end)
end
| uu____1264 -> begin
false
end)))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___160_1281 -> (match (uu___160_1281) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1282 -> begin
false
end)))))
end
| uu____1283 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1300) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1308) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1335) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1341) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___167_1350 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___167_1350.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___167_1350.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___167_1350.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___167_1350.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___161_1366 -> (match (uu___161_1366) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1367 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____1388 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1395, uu____1396) -> begin
(unascribe e2)
end
| uu____1425 -> begin
e1
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1470, uu____1471) -> begin
(ascribe t' k)
end
| uu____1500 -> begin
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
| uu____1523 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1528 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1533 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let canon_app = (fun t -> (

let uu____1554 = (

let uu____1562 = (unascribe t)
in (head_and_args' uu____1562))
in (match (uu____1554) with
| (hd1, args) -> begin
(FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end)))
in (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___162_1588 -> (match (uu___162_1588) with
| true -> begin
Equal
end
| uu____1589 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___163_1593 -> (match (uu___163_1593) with
| true -> begin
Equal
end
| uu____1594 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____1607 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____1615) -> begin
NotEqual
end
| (uu____1616, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____1617) -> begin
Unknown
end
| (uu____1618, Unknown) -> begin
Unknown
end))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____1623 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____1623))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____1636 = (eq_tm f g)
in (eq_and uu____1636 (fun uu____1639 -> (

let uu____1640 = (eq_univs_list us vs)
in (equal_if uu____1640)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____1643 = (FStar_Const.eq_const c d)
in (equal_iff uu____1643))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____1645), FStar_Syntax_Syntax.Tm_uvar (u2, uu____1647)) -> begin
(

let uu____1680 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (equal_if uu____1680))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____1713 = (

let uu____1716 = (

let uu____1717 = (un_uinst h1)
in uu____1717.FStar_Syntax_Syntax.n)
in (

let uu____1720 = (

let uu____1721 = (un_uinst h2)
in uu____1721.FStar_Syntax_Syntax.n)
in ((uu____1716), (uu____1720))))
in (match (uu____1713) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((f1.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) && (f2.FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) -> begin
(

let uu____1728 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____1728) with
| true -> begin
(

let uu____1731 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____1769 -> (match (uu____1769) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____1786 = (eq_tm a1 a2)
in (eq_inj acc uu____1786))
end)) Equal) uu____1731))
end
| uu____1787 -> begin
NotEqual
end))
end
| uu____1788 -> begin
(

let uu____1791 = (eq_tm h1 h2)
in (eq_and uu____1791 (fun uu____1793 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____1796 = (eq_univs u v1)
in (equal_if uu____1796))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____1798), uu____1799) -> begin
(eq_tm t12 t21)
end
| (uu____1804, FStar_Syntax_Syntax.Tm_meta (t22, uu____1806)) -> begin
(eq_tm t11 t22)
end
| uu____1811 -> begin
Unknown
end)))))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____1835))::a11, ((b, uu____1838))::b1) -> begin
(

let uu____1876 = (eq_tm a b)
in (match (uu____1876) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____1877 -> begin
Unknown
end))
end
| uu____1878 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____1897) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1903, uu____1904) -> begin
(unrefine t2)
end
| uu____1933 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1938 = (

let uu____1939 = (unrefine t)
in uu____1939.FStar_Syntax_Syntax.n)
in (match (uu____1938) with
| FStar_Syntax_Syntax.Tm_type (uu____1942) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1945) -> begin
(is_unit t1)
end
| uu____1950 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1955 = (

let uu____1956 = (unrefine t)
in uu____1956.FStar_Syntax_Syntax.n)
in (match (uu____1955) with
| FStar_Syntax_Syntax.Tm_type (uu____1959) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1962) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1978) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1983, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____1995 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____2000 = (

let uu____2001 = (FStar_Syntax_Subst.compress e)
in uu____2001.FStar_Syntax_Syntax.n)
in (match (uu____2000) with
| FStar_Syntax_Syntax.Tm_abs (uu____2004) -> begin
true
end
| uu____2014 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2019 = (

let uu____2020 = (FStar_Syntax_Subst.compress t)
in uu____2020.FStar_Syntax_Syntax.n)
in (match (uu____2019) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2023) -> begin
true
end
| uu____2031 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2038) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2044, uu____2045) -> begin
(pre_typ t2)
end
| uu____2074 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____2090 = (

let uu____2091 = (un_uinst typ1)
in uu____2091.FStar_Syntax_Syntax.n)
in (match (uu____2090) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____2129 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____2145 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____2157, lids, uu____2159) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____2164, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2171, uu____2172, uu____2173, uu____2174, uu____2175) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____2181, uu____2182, uu____2183, uu____2184) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2188, uu____2189, uu____2190, uu____2191, uu____2192) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2196, uu____2197) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2199, uu____2200) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2203) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____2204) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____2205) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2214 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb = (fun uu___164_2241 -> (match (uu___164_2241) with
| (FStar_Util.Inl (x), uu____2248, uu____2249) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____2253, uu____2254) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun uu____2275 -> (match (uu____2275) with
| (hd1, uu____2281) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(

let uu____2408 = (

let uu____2411 = (

let uu____2412 = (

let uu____2417 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2417), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____2412))
in (FStar_Syntax_Syntax.mk uu____2411))
in (uu____2408 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)))
end
| uu____2426 -> begin
(

let e = (

let uu____2435 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____2435 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____2452 = (

let uu____2455 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____2455), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2452))
end
| uu____2456 -> begin
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
| uu____2480 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____2496 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2496) with
| true -> begin
(

let uu____2497 = (

let uu____2500 = (

let uu____2501 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____2501))
in (

let uu____2502 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____2500), (uu____2502))))
in (FStar_Ident.mk_ident uu____2497))
end
| uu____2503 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___168_2505 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___168_2505.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___168_2505.FStar_Syntax_Syntax.sort})
in (

let uu____2506 = (mk_field_projector_name_from_ident lid nm)
in ((uu____2506), (y))))))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uv t -> (

let uu____2515 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____2515) with
| FStar_Pervasives_Native.Some (uu____2517) -> begin
(

let uu____2518 = (

let uu____2519 = (

let uu____2520 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2520))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2519))
in (failwith uu____2518))
end
| uu____2521 -> begin
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
| uu____2609 -> begin
(q1 = q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____2635 = (

let uu___169_2636 = rc
in (

let uu____2637 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___169_2636.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____2637; FStar_Syntax_Syntax.residual_flags = uu___169_2636.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____2635))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____2645 -> begin
(

let body = (

let uu____2647 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____2647))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____2665 = (

let uu____2668 = (

let uu____2669 = (

let uu____2679 = (

let uu____2683 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____2683 bs'))
in (

let uu____2689 = (close_lopt lopt')
in ((uu____2679), (t1), (uu____2689))))
in FStar_Syntax_Syntax.Tm_abs (uu____2669))
in (FStar_Syntax_Syntax.mk uu____2668))
in (uu____2665 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____2705 -> begin
(

let uu____2709 = (

let uu____2712 = (

let uu____2713 = (

let uu____2723 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2724 = (close_lopt lopt)
in ((uu____2723), (body), (uu____2724))))
in FStar_Syntax_Syntax.Tm_abs (uu____2713))
in (FStar_Syntax_Syntax.mk uu____2712))
in (uu____2709 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____2759 -> begin
(

let uu____2763 = (

let uu____2766 = (

let uu____2767 = (

let uu____2775 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2776 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____2775), (uu____2776))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2767))
in (FStar_Syntax_Syntax.mk uu____2766))
in (uu____2763 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____2808 = (

let uu____2809 = (FStar_Syntax_Subst.compress t)
in uu____2809.FStar_Syntax_Syntax.n)
in (match (uu____2808) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____2829) -> begin
(

let uu____2836 = (

let uu____2837 = (FStar_Syntax_Subst.compress tres)
in uu____2837.FStar_Syntax_Syntax.n)
in (match (uu____2836) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(

let uu____2854 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) uu____2854 t.FStar_Syntax_Syntax.pos))
end
| uu____2870 -> begin
t
end))
end
| uu____2871 -> begin
t
end)
end
| uu____2872 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____2883 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (

let uu____2888 = (

let uu____2889 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____2889 t.FStar_Syntax_Syntax.pos))
in (

let uu____2890 = (

let uu____2893 = (

let uu____2894 = (

let uu____2899 = (

let uu____2900 = (

let uu____2901 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2901)::[])
in (FStar_Syntax_Subst.close uu____2900 t))
in ((b), (uu____2899)))
in FStar_Syntax_Syntax.Tm_refine (uu____2894))
in (FStar_Syntax_Syntax.mk uu____2893))
in (uu____2890 uu____2883 uu____2888)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2941 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2941) with
| (bs1, c1) -> begin
(

let uu____2951 = (is_tot_or_gtot_comp c1)
in (match (uu____2951) with
| true -> begin
(

let uu____2957 = (arrow_formals_comp (comp_result c1))
in (match (uu____2957) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____2981 -> begin
((bs1), (c1))
end))
end))
end
| uu____2982 -> begin
(

let uu____2983 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2983)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____3000 = (arrow_formals_comp k)
in (match (uu____3000) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3048 = (

let uu___170_3049 = rc
in (

let uu____3050 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___170_3049.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3050; FStar_Syntax_Syntax.residual_flags = uu___170_3049.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3048))
end
| uu____3056 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____3074 = (

let uu____3075 = (

let uu____3078 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____3078))
in uu____3075.FStar_Syntax_Syntax.n)
in (match (uu____3074) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____3101 = (aux t2 what)
in (match (uu____3101) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____3133 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____3140 = (aux t FStar_Pervasives_Native.None)
in (match (uu____3140) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____3163 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____3163) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____3249) -> begin
def
end
| (uu____3255, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____3262) -> begin
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

let uu____3323 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____3323) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____3339 -> begin
(

let t' = (arrow binders c)
in (

let uu____3346 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____3346) with
| (uvs1, t'1) -> begin
(

let uu____3357 = (

let uu____3358 = (FStar_Syntax_Subst.compress t'1)
in uu____3358.FStar_Syntax_Syntax.n)
in (match (uu____3357) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____3384 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____3396 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____3402 -> begin
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

let uu____3439 = (

let uu____3440 = (pre_typ t)
in uu____3440.FStar_Syntax_Syntax.n)
in (match (uu____3439) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____3444 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3453 = (

let uu____3454 = (pre_typ t)
in uu____3454.FStar_Syntax_Syntax.n)
in (match (uu____3453) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3457) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____3459) -> begin
(is_constructed_typ t1 lid)
end
| uu____3474 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____3482) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____3483) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3484) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3486) -> begin
(get_tycon t2)
end
| uu____3501 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3512 = (

let uu____3513 = (un_uinst t)
in uu____3513.FStar_Syntax_Syntax.n)
in (match (uu____3512) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid)
end
| uu____3517 -> begin
false
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____3522 = (

let uu____3523 = (un_uinst t)
in uu____3523.FStar_Syntax_Syntax.n)
in (match (uu____3522) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____3527 -> begin
false
end)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____3545 -> (

let u = (

let uu____3549 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_27 -> FStar_Syntax_Syntax.U_unif (_0_27)) uu____3549))
in (

let uu____3558 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____3558), (u)))))


let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


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

let uu____3624 = (

let uu____3627 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3628 = (

let uu____3631 = (

let uu____3632 = (

let uu____3642 = (

let uu____3644 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____3645 = (

let uu____3647 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3647)::[])
in (uu____3644)::uu____3645))
in ((tand), (uu____3642)))
in FStar_Syntax_Syntax.Tm_app (uu____3632))
in (FStar_Syntax_Syntax.mk uu____3631))
in (uu____3628 FStar_Pervasives_Native.None uu____3627)))
in FStar_Pervasives_Native.Some (uu____3624))
end))


let mk_binop = (fun op_t phi1 phi2 -> (

let uu____3686 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3687 = (

let uu____3690 = (

let uu____3691 = (

let uu____3701 = (

let uu____3703 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____3704 = (

let uu____3706 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3706)::[])
in (uu____3703)::uu____3704))
in ((op_t), (uu____3701)))
in FStar_Syntax_Syntax.Tm_app (uu____3691))
in (FStar_Syntax_Syntax.mk uu____3690))
in (uu____3687 FStar_Pervasives_Native.None uu____3686))))


let mk_neg = (fun phi -> (

let uu____3729 = (

let uu____3732 = (

let uu____3733 = (

let uu____3743 = (

let uu____3745 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____3745)::[])
in ((t_not), (uu____3743)))
in FStar_Syntax_Syntax.Tm_app (uu____3733))
in (FStar_Syntax_Syntax.mk uu____3732))
in (uu____3729 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_conj tl1 hd1)
end))


let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_disj tl1 hd1)
end))


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop timp phi1 phi2))


let mk_iff : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t = (fun e -> (

let uu____3834 = (

let uu____3837 = (

let uu____3838 = (

let uu____3848 = (

let uu____3850 = (FStar_Syntax_Syntax.as_arg e)
in (uu____3850)::[])
in ((b2t_v), (uu____3848)))
in FStar_Syntax_Syntax.Tm_app (uu____3838))
in (FStar_Syntax_Syntax.mk uu____3837))
in (uu____3834 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 = (fun e1 e2 -> (

let uu____3877 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3878 = (

let uu____3881 = (

let uu____3882 = (

let uu____3892 = (

let uu____3894 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3895 = (

let uu____3897 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3897)::[])
in (uu____3894)::uu____3895))
in ((teq), (uu____3892)))
in FStar_Syntax_Syntax.Tm_app (uu____3882))
in (FStar_Syntax_Syntax.mk uu____3881))
in (uu____3878 FStar_Pervasives_Native.None uu____3877))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____3924 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3925 = (

let uu____3928 = (

let uu____3929 = (

let uu____3939 = (

let uu____3941 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3942 = (

let uu____3944 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3945 = (

let uu____3947 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3947)::[])
in (uu____3944)::uu____3945))
in (uu____3941)::uu____3942))
in ((eq_inst), (uu____3939)))
in FStar_Syntax_Syntax.Tm_app (uu____3929))
in (FStar_Syntax_Syntax.mk uu____3928))
in (uu____3925 FStar_Pervasives_Native.None uu____3924)))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____3989 = (

let uu____3992 = (

let uu____3993 = (

let uu____4003 = (

let uu____4005 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____4006 = (

let uu____4008 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____4009 = (

let uu____4011 = (FStar_Syntax_Syntax.as_arg t')
in (uu____4011)::[])
in (uu____4008)::uu____4009))
in (uu____4005)::uu____4006))
in ((t_has_type1), (uu____4003)))
in FStar_Syntax_Syntax.Tm_app (uu____3993))
in (FStar_Syntax_Syntax.mk uu____3992))
in (uu____3989 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (

let uu____4025 = (

let uu____4028 = (

let uu____4029 = (

let uu____4034 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____4034), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4029))
in (FStar_Syntax_Syntax.mk uu____4028))
in (uu____4025 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____4052 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____4059) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____4066) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____4052) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____4080 -> c0)}
end)))


let mk_residual_comp : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux = (fun fa x body -> (

let uu____4150 = (

let uu____4153 = (

let uu____4154 = (

let uu____4164 = (

let uu____4166 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____4167 = (

let uu____4169 = (

let uu____4170 = (

let uu____4171 = (

let uu____4172 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4172)::[])
in (abs uu____4171 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____4170))
in (uu____4169)::[])
in (uu____4166)::uu____4167))
in ((fa), (uu____4164)))
in FStar_Syntax_Syntax.Tm_app (uu____4154))
in (FStar_Syntax_Syntax.mk uu____4153))
in (uu____4150 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____4220 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____4220) with
| true -> begin
f1
end
| uu____4221 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____4228) -> begin
true
end
| uu____4229 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (

let uu____4275 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____4275), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____4295 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____4295), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____4305 = (

let uu____4306 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4306))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____4305)))))


let mk_squash = (fun p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____4362 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____4365 = (

let uu____4371 = (FStar_Syntax_Syntax.as_arg p)
in (uu____4371)::[])
in (mk_app uu____4362 uu____4365)))))


let un_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____4379 = (head_and_args t)
in (match (uu____4379) with
| (head1, args) -> begin
(

let uu____4408 = (

let uu____4416 = (

let uu____4417 = (un_uinst head1)
in uu____4417.FStar_Syntax_Syntax.n)
in ((uu____4416), (args)))
in (match (uu____4408) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____4430))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____4469 = (

let uu____4472 = (

let uu____4473 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____4473)::[])
in (FStar_Syntax_Subst.open_term uu____4472 p))
in (match (uu____4469) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____4491 -> begin
(failwith "impossible")
end)
in (

let uu____4494 = (

let uu____4495 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____4495))
in (match (uu____4494) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4502 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____4503 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____4506 -> begin
FStar_Pervasives_Native.None
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____4526 = (

let uu____4527 = (FStar_Syntax_Subst.compress t)
in uu____4527.FStar_Syntax_Syntax.n)
in (match (uu____4526) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____4588 = (

let uu____4593 = (

let uu____4594 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____4594))
in ((b), (uu____4593)))
in FStar_Pervasives_Native.Some (uu____4588))
end
| uu____4601 -> begin
FStar_Pervasives_Native.None
end)))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____4612 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____4612)))


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
| uu____4643 -> begin
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
| uu____4669 -> begin
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
| uu____4694 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____4721)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____4731)) -> begin
(unmeta_monadic t)
end
| uu____4741 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____4786 -> (match (uu____4786) with
| (lid, arity) -> begin
(

let uu____4792 = (

let uu____4802 = (unmeta_monadic f2)
in (head_and_args uu____4802))
in (match (uu____4792) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____4821 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____4821) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____4840 -> begin
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

let uu____4876 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____4876)))
end
| uu____4883 -> begin
(

let uu____4884 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____4884)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4908 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____4918 = (head_and_args t1)
in (match (uu____4918) with
| (t2, args) -> begin
(

let uu____4949 = (un_uinst t2)
in (

let uu____4950 = (FStar_All.pipe_right args (FStar_List.map (fun uu____4970 -> (match (uu____4970) with
| (t3, imp) -> begin
(

let uu____4977 = (unascribe t3)
in ((uu____4977), (imp)))
end))))
in ((uu____4949), (uu____4950))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____5000 = (

let uu____5009 = (flat t1)
in ((qopt), (uu____5009)))
in (match (uu____5000) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____5024; FStar_Syntax_Syntax.pos = uu____5025; FStar_Syntax_Syntax.vars = uu____5026}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____5029); FStar_Syntax_Syntax.tk = uu____5030; FStar_Syntax_Syntax.pos = uu____5031; FStar_Syntax_Syntax.vars = uu____5032}, uu____5033))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____5084; FStar_Syntax_Syntax.pos = uu____5085; FStar_Syntax_Syntax.vars = uu____5086}, (uu____5087)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____5090); FStar_Syntax_Syntax.tk = uu____5091; FStar_Syntax_Syntax.pos = uu____5092; FStar_Syntax_Syntax.vars = uu____5093}, uu____5094))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____5152; FStar_Syntax_Syntax.pos = uu____5153; FStar_Syntax_Syntax.vars = uu____5154}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____5157); FStar_Syntax_Syntax.tk = uu____5158; FStar_Syntax_Syntax.pos = uu____5159; FStar_Syntax_Syntax.vars = uu____5160}, uu____5161))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____5211; FStar_Syntax_Syntax.pos = uu____5212; FStar_Syntax_Syntax.vars = uu____5213}, (uu____5214)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____5217); FStar_Syntax_Syntax.tk = uu____5218; FStar_Syntax_Syntax.pos = uu____5219; FStar_Syntax_Syntax.vars = uu____5220}, uu____5221))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (b), uu____5279) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____5297 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____5297) with
| (bs1, t2) -> begin
(

let uu____5303 = (patterns t2)
in (match (uu____5303) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____5334 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____5341 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____5377 = (un_squash t)
in (FStar_Util.bind_opt uu____5377 (fun t1 -> (

let uu____5392 = (head_and_args' t1)
in (match (uu____5392) with
| (hd1, args) -> begin
(

let uu____5413 = (

let uu____5416 = (

let uu____5417 = (un_uinst hd1)
in uu____5417.FStar_Syntax_Syntax.n)
in ((uu____5416), ((FStar_List.length args))))
in (match (uu____5413) with
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
| uu____5477 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____5494 = (un_squash t)
in (FStar_Util.bind_opt uu____5494 (fun t1 -> (

let uu____5508 = (arrow_one t1)
in (match (uu____5508) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____5517 = (

let uu____5518 = (is_tot_or_gtot_comp c)
in (not (uu____5518)))
in (match (uu____5517) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5520 -> begin
(

let q = (

let uu____5524 = (comp_to_comp_typ c)
in uu____5524.FStar_Syntax_Syntax.result_typ)
in (

let uu____5525 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____5525) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5543 -> begin
(failwith "impossible")
end)
in (

let uu____5546 = (is_free_in (FStar_Pervasives_Native.fst b1) q1)
in (match (uu____5546) with
| true -> begin
(

let uu____5548 = (patterns q1)
in (match (uu____5548) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b1)::[]), (pats), (q2))))))
end))
end
| uu____5587 -> begin
(

let uu____5588 = (

let uu____5589 = (

let uu____5592 = (

let uu____5594 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort)
in (

let uu____5595 = (

let uu____5597 = (FStar_Syntax_Syntax.as_arg q1)
in (uu____5597)::[])
in (uu____5594)::uu____5595))
in ((FStar_Parser_Const.imp_lid), (uu____5592)))
in BaseConn (uu____5589))
in FStar_Pervasives_Native.Some (uu____5588))
end)))
end)))
end))
end
| uu____5599 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____5604 = (un_squash t)
in (FStar_Util.bind_opt uu____5604 (fun t1 -> (

let uu____5634 = (head_and_args' t1)
in (match (uu____5634) with
| (hd1, args) -> begin
(

let uu____5655 = (

let uu____5663 = (

let uu____5664 = (un_uinst hd1)
in uu____5664.FStar_Syntax_Syntax.n)
in ((uu____5663), (args)))
in (match (uu____5655) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____5675))::((a2, uu____5677))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____5703 = (

let uu____5704 = (FStar_Syntax_Subst.compress a2)
in uu____5704.FStar_Syntax_Syntax.n)
in (match (uu____5703) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____5710) -> begin
(

let uu____5726 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____5726) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5748 -> begin
(failwith "impossible")
end)
in (

let uu____5751 = (patterns q1)
in (match (uu____5751) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____5790 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____5791 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____5805 = (destruct_sq_forall phi)
in (match (uu____5805) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_36 -> FStar_Pervasives_Native.Some (_0_36)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____5818 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____5823 = (destruct_sq_exists phi)
in (match (uu____5823) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____5836 -> begin
f1
end))
end
| uu____5838 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____5841 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____5841 (fun uu____5845 -> (

let uu____5846 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____5846 (fun uu____5850 -> (

let uu____5851 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____5851 (fun uu____5855 -> (

let uu____5856 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____5856 (fun uu____5860 -> (

let uu____5861 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____5861 (fun uu____5864 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____5874 = (

let uu____5877 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____5877))
in (

let uu____5878 = (

let uu____5879 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____5879))
in (

let uu____5882 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____5874 a.FStar_Syntax_Syntax.action_univs uu____5878 FStar_Parser_Const.effect_Tot_lid uu____5882))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]), ([]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____5912 = (

let uu____5915 = (

let uu____5916 = (

let uu____5926 = (

let uu____5928 = (FStar_Syntax_Syntax.as_arg t)
in (uu____5928)::[])
in ((reify_), (uu____5926)))
in FStar_Syntax_Syntax.Tm_app (uu____5916))
in (FStar_Syntax_Syntax.mk uu____5915))
in (uu____5912 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____5945) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____5961) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____5962) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____5963) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____5978) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____5989) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____5990) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5991) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____6000) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6005; FStar_Syntax_Syntax.index = uu____6006; FStar_Syntax_Syntax.sort = t2}, uu____6008) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____6016) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____6022, uu____6023) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____6053) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____6068, t2, uu____6070) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____6083, t2) -> begin
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

let uu____6105 = (delta_qualifier t)
in (incr_delta_depth uu____6105)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____6110 = (

let uu____6111 = (FStar_Syntax_Subst.compress t)
in uu____6111.FStar_Syntax_Syntax.n)
in (match (uu____6110) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____6114 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____6123 = (

let uu____6133 = (unmeta e)
in (head_and_args uu____6133))
in (match (uu____6123) with
| (head1, args) -> begin
(

let uu____6152 = (

let uu____6160 = (

let uu____6161 = (un_uinst head1)
in uu____6161.FStar_Syntax_Syntax.n)
in ((uu____6160), (args)))
in (match (uu____6152) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____6172) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6185)::((hd1, uu____6187))::((tl1, uu____6189))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____6223 = (

let uu____6227 = (

let uu____6231 = (list_elements tl1)
in (FStar_Util.must uu____6231))
in (hd1)::uu____6227)
in FStar_Pervasives_Native.Some (uu____6223))
end
| uu____6240 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____6274 = (f a)
in (uu____6274)::[])
end
| (x)::xs -> begin
(

let uu____6278 = (apply_last f xs)
in (x)::uu____6278)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____6314 = (

let uu____6317 = (

let uu____6318 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____6318))
in (FStar_Syntax_Syntax.mk uu____6317))
in (uu____6314 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____6336 = (

let uu____6337 = (

let uu____6338 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6338 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6337 args))
in (uu____6336 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____6352 = (

let uu____6353 = (

let uu____6354 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6354 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6353 args))
in (uu____6352 FStar_Pervasives_Native.None pos)))
in (

let uu____6359 = (

let uu____6360 = (

let uu____6361 = (FStar_Syntax_Syntax.iarg typ)
in (uu____6361)::[])
in (nil uu____6360 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____6367 = (

let uu____6368 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____6369 = (

let uu____6371 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____6372 = (

let uu____6374 = (FStar_Syntax_Syntax.as_arg a)
in (uu____6374)::[])
in (uu____6371)::uu____6372))
in (uu____6368)::uu____6369))
in (cons1 uu____6367 t.FStar_Syntax_Syntax.pos))) l uu____6359))))))


let uvar_from_id = (fun id t -> (

let uu____6392 = (

let uu____6395 = (

let uu____6396 = (

let uu____6407 = (FStar_Syntax_Unionfind.from_id id)
in ((uu____6407), (t)))
in FStar_Syntax_Syntax.Tm_uvar (uu____6396))
in (FStar_Syntax_Syntax.mk uu____6395))
in (uu____6392 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let rec eqlist = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____6463 -> begin
false
end))


let eqsum = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____6542 -> begin
false
end))


let eqprod = (fun e1 e2 x y -> (match (((x), (y))) with
| ((x1, x2), (y1, y2)) -> begin
((e1 x1 y1) && (e2 x2 y2))
end))


let eqopt = (fun e x y -> (match (((x), (y))) with
| (FStar_Pervasives_Native.Some (x1), FStar_Pervasives_Native.Some (y1)) -> begin
(e x1 y1)
end
| uu____6660 -> begin
false
end))


let rec term_eq : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun t1 t2 -> (

let canon_app = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____6755) -> begin
(

let uu____6765 = (head_and_args' t)
in (match (uu____6765) with
| (hd1, args) -> begin
(

let uu___171_6787 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args))); FStar_Syntax_Syntax.tk = uu___171_6787.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___171_6787.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___171_6787.FStar_Syntax_Syntax.vars})
end))
end
| uu____6799 -> begin
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
| (uu____6995, uu____6996) -> begin
false
end)))))
and arg_eq : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun a1 a2 -> (eqprod term_eq (fun q1 q2 -> (q1 = q2)) a1 a2))
and binder_eq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun b1 b2 -> (eqprod (fun b11 b21 -> (term_eq b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)) (fun q1 q2 -> (q1 = q2)) b1 b2))
and lcomp_eq : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> false)
and residual_eq : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> false)
and comp_eq : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c1 c2 -> (match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Total (t1, u1), FStar_Syntax_Syntax.Total (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.GTotal (t1, u1), FStar_Syntax_Syntax.GTotal (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.Comp (c11), FStar_Syntax_Syntax.Comp (c21)) -> begin
(((((c11.FStar_Syntax_Syntax.comp_univs = c21.FStar_Syntax_Syntax.comp_univs) && (c11.FStar_Syntax_Syntax.effect_name = c21.FStar_Syntax_Syntax.effect_name)) && (term_eq c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)) && (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args c21.FStar_Syntax_Syntax.effect_args)) && (eq_flags c11.FStar_Syntax_Syntax.flags c21.FStar_Syntax_Syntax.flags))
end
| (uu____7075, uu____7076) -> begin
false
end))
and eq_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  Prims.bool = (fun f1 f2 -> false)
and branch_eq : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun uu____7081 uu____7082 -> (match (((uu____7081), (uu____7082))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
false
end))


let rec bottom_fold : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun f t -> (

let ff = (bottom_fold f)
in (

let tn = (

let uu____7184 = (FStar_Syntax_Subst.compress t)
in uu____7184.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (f1, args) -> begin
(

let uu____7204 = (

let uu____7214 = (ff f1)
in (

let uu____7215 = (FStar_List.map (fun uu____7227 -> (match (uu____7227) with
| (a, q) -> begin
(

let uu____7234 = (ff a)
in ((uu____7234), (q)))
end)) args)
in ((uu____7214), (uu____7215))))
in FStar_Syntax_Syntax.Tm_app (uu____7204))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____7253 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____7253) with
| (bs1, t') -> begin
(

let t'' = (ff t')
in (

let uu____7259 = (

let uu____7269 = (FStar_Syntax_Subst.close bs1 t'')
in ((bs1), (uu____7269), (k)))
in FStar_Syntax_Syntax.Tm_abs (uu____7259)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
tn
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____7289 = (

let uu____7294 = (ff t1)
in ((uu____7294), (us)))
in FStar_Syntax_Syntax.Tm_uinst (uu____7289))
end
| uu____7295 -> begin
tn
end)
in (f (

let uu___172_7298 = t
in {FStar_Syntax_Syntax.n = tn1; FStar_Syntax_Syntax.tk = uu___172_7298.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___172_7298.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___172_7298.FStar_Syntax_Syntax.vars}))))))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____7307) -> begin
(

let uu____7322 = (

let uu____7323 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____7323))
in ((Prims.parse_int "1") + uu____7322))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____7325 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____7325))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____7327 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____7327))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____7334 = (sizeof t1)
in ((FStar_List.length us) + uu____7334))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____7343) -> begin
(

let uu____7356 = (sizeof t1)
in (

let uu____7357 = (FStar_List.fold_left (fun acc uu____7366 -> (match (uu____7366) with
| (bv, uu____7370) -> begin
(

let uu____7371 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____7371))
end)) (Prims.parse_int "0") bs)
in (uu____7356 + uu____7357)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____7388 = (sizeof hd1)
in (

let uu____7389 = (FStar_List.fold_left (fun acc uu____7398 -> (match (uu____7398) with
| (arg, uu____7402) -> begin
(

let uu____7403 = (sizeof arg)
in (acc + uu____7403))
end)) (Prims.parse_int "0") args)
in (uu____7388 + uu____7389)))
end
| uu____7404 -> begin
(Prims.parse_int "1")
end))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____7409 = (

let uu____7410 = (un_uinst t)
in uu____7410.FStar_Syntax_Syntax.n)
in (match (uu____7409) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid)
end
| uu____7414 -> begin
false
end)))


let mk_alien = (fun b s r -> (

let uu____7438 = (

let uu____7441 = (

let uu____7442 = (

let uu____7447 = (

let uu____7448 = (

let uu____7451 = (FStar_Dyn.mkdyn b)
in ((uu____7451), (s)))
in FStar_Syntax_Syntax.Meta_alien (uu____7448))
in ((FStar_Syntax_Syntax.tun), (uu____7447)))
in FStar_Syntax_Syntax.Tm_meta (uu____7442))
in (FStar_Syntax_Syntax.mk uu____7441))
in (uu____7438 FStar_Pervasives_Native.None (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
r1
end
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end))))


let un_alien : FStar_Syntax_Syntax.term  ->  FStar_Dyn.dyn = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____7468, FStar_Syntax_Syntax.Meta_alien (blob, uu____7470)) -> begin
blob
end
| uu____7475 -> begin
(failwith "Something paranormal occurred")
end))




