
open Prims
open FStar_Pervasives

let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (

let uu____7 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range uu____7 id.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder = (fun uu____25 -> (match (uu____25) with
| (b, imp) -> begin
(

let uu____30 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____30), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____43 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____43) with
| true -> begin
[]
end
| uu____49 -> begin
(

let uu____50 = (arg_of_non_null_binder b)
in (uu____50)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____64 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____86 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____86) with
| true -> begin
(

let b1 = (

let uu____96 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____96), ((FStar_Pervasives_Native.snd b))))
in (

let uu____97 = (arg_of_non_null_binder b1)
in ((b1), (uu____97))))
end
| uu____104 -> begin
(

let uu____105 = (arg_of_non_null_binder b)
in ((b), (uu____105)))
end)))))
in (FStar_All.pipe_right uu____64 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____145 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____145) with
| true -> begin
(

let uu____148 = b
in (match (uu____148) with
| (a, imp) -> begin
(

let b1 = (

let uu____154 = (

let uu____155 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____155))
in (FStar_Ident.id_of_text uu____154))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____157 -> begin
b
end))))))


let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____183 = (

let uu____186 = (

let uu____187 = (

let uu____195 = (name_binders binders)
in ((uu____195), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____187))
in (FStar_Syntax_Syntax.mk uu____186))
in (uu____183 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____212 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____232 -> (match (uu____232) with
| (t, imp) -> begin
(

let uu____239 = (

let uu____240 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____240))
in ((uu____239), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____266 -> (match (uu____266) with
| (t, imp) -> begin
(

let uu____279 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____279), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____286 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____286 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____335 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match (((FStar_List.length replace_xs) = (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____354 uu____355 -> (match (((uu____354), (uu____355))) with
| ((x, uu____365), (y, uu____367)) -> begin
(

let uu____372 = (

let uu____377 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____377)))
in FStar_Syntax_Syntax.NT (uu____372))
end)) replace_xs with_ys)
end
| uu____378 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____384) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____390, uu____391) -> begin
(unmeta e2)
end
| uu____420 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____428) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____429) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____433 = (univ_kernel u1)
in (match (uu____433) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____440) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____444) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____450 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____450)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____459), uu____460) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____461, FStar_Syntax_Syntax.U_bvar (uu____462)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____463) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____464, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____465) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____466, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____469), FStar_Syntax_Syntax.U_unif (uu____470)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____473), FStar_Syntax_Syntax.U_name (uu____474)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____483 = (FStar_Unionfind.uvar_id u11)
in (

let uu____485 = (FStar_Unionfind.uvar_id u21)
in (uu____483 - uu____485)))
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
| uu____504 -> begin
(

let copt = (

let uu____507 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____507 (fun uu____513 -> (match (uu____513) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((c <> (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____521 -> begin
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
| (FStar_Syntax_Syntax.U_max (uu____523), uu____524) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____526, FStar_Syntax_Syntax.U_max (uu____527)) -> begin
(Prims.parse_int "1")
end
| uu____529 -> begin
(

let uu____532 = (univ_kernel u1)
in (match (uu____532) with
| (k1, n1) -> begin
(

let uu____537 = (univ_kernel u2)
in (match (uu____537) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((r = (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____543 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____550 = (compare_univs u1 u2)
in (uu____550 = (Prims.parse_int "0"))))


let ml_comp : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____577) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____583) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____601) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____607) -> begin
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

let uu____637 = (

let uu____638 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____638))
in {FStar_Syntax_Syntax.comp_univs = uu____637; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____656 = (

let uu____657 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____657))
in {FStar_Syntax_Syntax.comp_univs = uu____656; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end))
in (

let uu___163_667 = c
in (

let uu____668 = (

let uu____669 = (

let uu___164_670 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___164_670.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___164_670.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___164_670.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___164_670.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____669))
in {FStar_Syntax_Syntax.n = uu____668; FStar_Syntax_Syntax.tk = uu___163_667.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___163_667.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___163_667.FStar_Syntax_Syntax.vars}))))


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
| uu____701 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____714) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____720) -> begin
false
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___151_738 -> (match (uu___151_738) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____739 -> begin
false
end)))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___152_744 -> (match (uu___152_744) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____745 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___153_750 -> (match (uu___153_750) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____751 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___154_764 -> (match (uu___154_764) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____765 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___155_770 -> (match (uu___155_770) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____771 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____797) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____803) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___156_811 -> (match (uu___156_811) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____812 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___157_831 -> (match (uu___157_831) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____832 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____839 = (

let uu____840 = (FStar_Syntax_Subst.compress t)
in uu____840.FStar_Syntax_Syntax.n)
in (match (uu____839) with
| FStar_Syntax_Syntax.Tm_arrow (uu____843, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____855 -> begin
true
end)))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____859 = (

let uu____860 = (FStar_Syntax_Subst.compress t)
in uu____860.FStar_Syntax_Syntax.n)
in (match (uu____859) with
| FStar_Syntax_Syntax.Tm_arrow (uu____863, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____876 -> begin
false
end)
end
| uu____877 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____923 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____938) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____943 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____947 = (

let uu____948 = (FStar_Syntax_Subst.compress t)
in uu____948.FStar_Syntax_Syntax.n)
in (match (uu____947) with
| FStar_Syntax_Syntax.Tm_arrow (uu____951, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____967))::uu____968 -> begin
(

let pats' = (unmeta pats)
in (

let uu____999 = (head_and_args pats')
in (match (uu____999) with
| (head1, uu____1010) -> begin
(

let uu____1025 = (

let uu____1026 = (un_uinst head1)
in uu____1026.FStar_Syntax_Syntax.n)
in (match (uu____1025) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1030 -> begin
false
end))
end)))
end
| uu____1031 -> begin
false
end)
end
| uu____1037 -> begin
false
end)
end
| uu____1038 -> begin
false
end)))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___158_1052 -> (match (uu___158_1052) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1053 -> begin
false
end)))))
end
| uu____1054 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1069) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1077) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1101) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1107) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___165_1114 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___165_1114.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___165_1114.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___165_1114.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___165_1114.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___159_1127 -> (match (uu___159_1127) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1128 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____1150 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1156, uu____1157) -> begin
(unascribe e2)
end
| uu____1186 -> begin
e1
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1228, uu____1229) -> begin
(ascribe t' k)
end
| uu____1258 -> begin
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
| uu____1280 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1284 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1288 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (unascribe t1)
in (

let t21 = (unascribe t2)
in (

let equal_if = (fun uu___160_1308 -> (match (uu___160_1308) with
| true -> begin
Equal
end
| uu____1309 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___161_1313 -> (match (uu___161_1313) with
| true -> begin
Equal
end
| uu____1314 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____1327 -> begin
Unknown
end))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____1332 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____1332))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____1345 = (eq_tm f g)
in (eq_and uu____1345 (fun uu____1346 -> (

let uu____1347 = (eq_univs_list us vs)
in (equal_if uu____1347)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____1350 = (FStar_Const.eq_const c d)
in (equal_iff uu____1350))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____1352), FStar_Syntax_Syntax.Tm_uvar (u2, uu____1354)) -> begin
(

let uu____1379 = (FStar_Unionfind.equivalent u1 u2)
in (equal_if uu____1379))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____1415 = (eq_tm h1 h2)
in (eq_and uu____1415 (fun uu____1416 -> (eq_args args1 args2))))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____1419 = (eq_univs u v1)
in (equal_if uu____1419))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____1421), uu____1422) -> begin
(eq_tm t12 t21)
end
| (uu____1427, FStar_Syntax_Syntax.Tm_meta (t22, uu____1429)) -> begin
(eq_tm t11 t22)
end
| uu____1434 -> begin
Unknown
end)))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____1458))::a11, ((b, uu____1461))::b1) -> begin
(

let uu____1499 = (eq_tm a b)
in (match (uu____1499) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____1500 -> begin
Unknown
end))
end
| uu____1501 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____1515) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1521, uu____1522) -> begin
(unrefine t2)
end
| uu____1551 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1555 = (

let uu____1556 = (unrefine t)
in uu____1556.FStar_Syntax_Syntax.n)
in (match (uu____1555) with
| FStar_Syntax_Syntax.Tm_type (uu____1559) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1562) -> begin
(is_unit t1)
end
| uu____1567 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1571 = (

let uu____1572 = (unrefine t)
in uu____1572.FStar_Syntax_Syntax.n)
in (match (uu____1571) with
| FStar_Syntax_Syntax.Tm_type (uu____1575) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1578) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1594) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1599, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____1611 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____1615 = (

let uu____1616 = (FStar_Syntax_Subst.compress e)
in uu____1616.FStar_Syntax_Syntax.n)
in (match (uu____1615) with
| FStar_Syntax_Syntax.Tm_abs (uu____1619) -> begin
true
end
| uu____1634 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1638 = (

let uu____1639 = (FStar_Syntax_Subst.compress t)
in uu____1639.FStar_Syntax_Syntax.n)
in (match (uu____1638) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1642) -> begin
true
end
| uu____1650 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____1656) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1662, uu____1663) -> begin
(pre_typ t2)
end
| uu____1692 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____1706 = (

let uu____1707 = (un_uinst typ1)
in uu____1707.FStar_Syntax_Syntax.n)
in (match (uu____1706) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____1745 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____1761 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____1772, lids, uu____1774) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____1779, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____1786, uu____1787, uu____1788, uu____1789, uu____1790) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____1796, uu____1797, uu____1798, uu____1799) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____1803, uu____1804, uu____1805, uu____1806, uu____1807) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____1811, uu____1812) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____1814) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____1817) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____1818) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____1819) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____1827 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb = (fun uu___162_1849 -> (match (uu___162_1849) with
| (FStar_Util.Inl (x), uu____1856, uu____1857) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____1861, uu____1862) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun uu____1879 -> (match (uu____1879) with
| (hd1, uu____1885) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(

let uu____1999 = (

let uu____2002 = (

let uu____2003 = (

let uu____2008 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2008), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____2003))
in (FStar_Syntax_Syntax.mk uu____2002))
in (uu____1999 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)))
end
| uu____2017 -> begin
(

let e = (

let uu____2026 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____2026 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "^fname^")) with
| true -> begin
(

let uu____2041 = (

let uu____2044 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((uu____2044), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2041))
end
| uu____2045 -> begin
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
| uu____2064 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____2077 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2077) with
| true -> begin
(

let uu____2078 = (

let uu____2081 = (

let uu____2082 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____2082))
in (

let uu____2083 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____2081), (uu____2083))))
in (FStar_Ident.mk_ident uu____2078))
end
| uu____2084 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___166_2086 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___166_2086.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___166_2086.FStar_Syntax_Syntax.sort})
in (

let uu____2087 = (mk_field_projector_name_from_ident lid nm)
in ((uu____2087), (y))))))


let set_uvar = (fun uv t -> (

let uu____2104 = (FStar_Unionfind.find uv)
in (match (uu____2104) with
| FStar_Syntax_Syntax.Fixed (uu____2107) -> begin
(

let uu____2108 = (

let uu____2109 = (

let uu____2110 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2110))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2109))
in (failwith uu____2108))
end
| uu____2112 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
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
| uu____2175 -> begin
(q1 = q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
lopt1
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (uu____2232)) -> begin
lopt1
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
(

let uu____2253 = (

let uu____2259 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (uu____2259))
in FStar_Pervasives_Native.Some (uu____2253))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____2270 -> begin
(

let body = (

let uu____2272 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____2272))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____2315 = (

let uu____2318 = (

let uu____2319 = (

let uu____2334 = (

let uu____2338 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____2338 bs'))
in (

let uu____2344 = (close_lopt lopt')
in ((uu____2334), (t1), (uu____2344))))
in FStar_Syntax_Syntax.Tm_abs (uu____2319))
in (FStar_Syntax_Syntax.mk uu____2318))
in (uu____2315 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____2370 -> begin
(

let uu____2379 = (

let uu____2382 = (

let uu____2383 = (

let uu____2398 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2399 = (close_lopt lopt)
in ((uu____2398), (body), (uu____2399))))
in FStar_Syntax_Syntax.Tm_abs (uu____2383))
in (FStar_Syntax_Syntax.mk uu____2382))
in (uu____2379 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____2442 -> begin
(

let uu____2446 = (

let uu____2449 = (

let uu____2450 = (

let uu____2458 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2459 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____2458), (uu____2459))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2450))
in (FStar_Syntax_Syntax.mk uu____2449))
in (uu____2446 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____2489 = (

let uu____2490 = (FStar_Syntax_Subst.compress t)
in uu____2490.FStar_Syntax_Syntax.n)
in (match (uu____2489) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____2510) -> begin
(

let uu____2517 = (

let uu____2518 = (FStar_Syntax_Subst.compress tres)
in uu____2518.FStar_Syntax_Syntax.n)
in (match (uu____2517) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(

let uu____2535 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) uu____2535 t.FStar_Syntax_Syntax.pos))
end
| uu____2551 -> begin
t
end))
end
| uu____2552 -> begin
t
end)
end
| uu____2553 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____2562 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (

let uu____2567 = (

let uu____2568 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____2568 t.FStar_Syntax_Syntax.pos))
in (

let uu____2569 = (

let uu____2572 = (

let uu____2573 = (

let uu____2578 = (

let uu____2579 = (

let uu____2580 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2580)::[])
in (FStar_Syntax_Subst.close uu____2579 t))
in ((b), (uu____2578)))
in FStar_Syntax_Syntax.Tm_refine (uu____2573))
in (FStar_Syntax_Syntax.mk uu____2572))
in (uu____2569 uu____2562 uu____2567)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2618 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2618) with
| (bs1, c1) -> begin
(

let uu____2628 = (is_tot_or_gtot_comp c1)
in (match (uu____2628) with
| true -> begin
(

let uu____2634 = (arrow_formals_comp (comp_result c1))
in (match (uu____2634) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____2658 -> begin
((bs1), (c1))
end))
end))
end
| uu____2659 -> begin
(

let uu____2660 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2660)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____2676 = (arrow_formals_comp k)
in (match (uu____2676) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l1)) -> begin
(

let l2 = (

let uu___167_2757 = l1
in (

let uu____2758 = (FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___167_2757.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2758; FStar_Syntax_Syntax.cflags = uu___167_2757.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2761 -> (

let uu____2762 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____2762)))}))
in FStar_Pervasives_Native.Some (FStar_Util.Inl (l2)))
end
| uu____2771 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____2809 = (

let uu____2810 = (

let uu____2813 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____2813))
in uu____2810.FStar_Syntax_Syntax.n)
in (match (uu____2809) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____2851 = (aux t2 what)
in (match (uu____2851) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____2908 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____2920 = (aux t FStar_Pervasives_Native.None)
in (match (uu____2920) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____2968 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____2968) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____3058) -> begin
def
end
| (uu____3064, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____3071) -> begin
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

let uu____3132 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____3132) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____3148 -> begin
(

let t' = (arrow binders c)
in (

let uu____3155 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____3155) with
| (uvs1, t'1) -> begin
(

let uu____3166 = (

let uu____3167 = (FStar_Syntax_Subst.compress t'1)
in uu____3167.FStar_Syntax_Syntax.n)
in (match (uu____3166) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____3193 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____3208 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____3217 -> begin
false
end))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.not_lid)::(FStar_Parser_Const.iff_lid)::(FStar_Parser_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3252 = (

let uu____3253 = (pre_typ t)
in uu____3253.FStar_Syntax_Syntax.n)
in (match (uu____3252) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____3261 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3268 = (

let uu____3269 = (pre_typ t)
in uu____3269.FStar_Syntax_Syntax.n)
in (match (uu____3268) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3272) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____3274) -> begin
(is_constructed_typ t1 lid)
end
| uu____3289 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____3296) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____3297) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3298) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3300) -> begin
(get_tycon t2)
end
| uu____3315 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____3345 -> (

let u = (

let uu____3349 = (FStar_Unionfind.fresh FStar_Pervasives_Native.None)
in (FStar_All.pipe_left (fun _0_27 -> FStar_Syntax_Syntax.U_unif (_0_27)) uu____3349))
in (

let uu____3355 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____3355), (u)))))


let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string ((((FStar_Util.unicode_of_string s)), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.imp_lid)


let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.iff_lid)


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

let uu____3428 = (

let uu____3431 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3432 = (

let uu____3435 = (

let uu____3436 = (

let uu____3446 = (

let uu____3448 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____3449 = (

let uu____3451 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3451)::[])
in (uu____3448)::uu____3449))
in ((tand), (uu____3446)))
in FStar_Syntax_Syntax.Tm_app (uu____3436))
in (FStar_Syntax_Syntax.mk uu____3435))
in (uu____3432 FStar_Pervasives_Native.None uu____3431)))
in FStar_Pervasives_Native.Some (uu____3428))
end))


let mk_binop = (fun op_t phi1 phi2 -> (

let uu____3486 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3487 = (

let uu____3490 = (

let uu____3491 = (

let uu____3501 = (

let uu____3503 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____3504 = (

let uu____3506 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3506)::[])
in (uu____3503)::uu____3504))
in ((op_t), (uu____3501)))
in FStar_Syntax_Syntax.Tm_app (uu____3491))
in (FStar_Syntax_Syntax.mk uu____3490))
in (uu____3487 FStar_Pervasives_Native.None uu____3486))))


let mk_neg = (fun phi -> (

let uu____3527 = (

let uu____3530 = (

let uu____3531 = (

let uu____3541 = (

let uu____3543 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____3543)::[])
in ((t_not), (uu____3541)))
in FStar_Syntax_Syntax.Tm_app (uu____3531))
in (FStar_Syntax_Syntax.mk uu____3530))
in (uu____3527 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


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

let uu____3618 = (

let uu____3621 = (

let uu____3622 = (

let uu____3632 = (

let uu____3634 = (FStar_Syntax_Syntax.as_arg e)
in (uu____3634)::[])
in ((b2t_v), (uu____3632)))
in FStar_Syntax_Syntax.Tm_app (uu____3622))
in (FStar_Syntax_Syntax.mk uu____3621))
in (uu____3618 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 = (fun e1 e2 -> (

let uu____3658 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3659 = (

let uu____3662 = (

let uu____3663 = (

let uu____3673 = (

let uu____3675 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3676 = (

let uu____3678 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3678)::[])
in (uu____3675)::uu____3676))
in ((teq), (uu____3673)))
in FStar_Syntax_Syntax.Tm_app (uu____3663))
in (FStar_Syntax_Syntax.mk uu____3662))
in (uu____3659 FStar_Pervasives_Native.None uu____3658))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____3701 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3702 = (

let uu____3705 = (

let uu____3706 = (

let uu____3716 = (

let uu____3718 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3719 = (

let uu____3721 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3722 = (

let uu____3724 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3724)::[])
in (uu____3721)::uu____3722))
in (uu____3718)::uu____3719))
in ((eq_inst), (uu____3716)))
in FStar_Syntax_Syntax.Tm_app (uu____3706))
in (FStar_Syntax_Syntax.mk uu____3705))
in (uu____3702 FStar_Pervasives_Native.None uu____3701)))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____3762 = (

let uu____3765 = (

let uu____3766 = (

let uu____3776 = (

let uu____3778 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3779 = (

let uu____3781 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____3782 = (

let uu____3784 = (FStar_Syntax_Syntax.as_arg t')
in (uu____3784)::[])
in (uu____3781)::uu____3782))
in (uu____3778)::uu____3779))
in ((t_has_type1), (uu____3776)))
in FStar_Syntax_Syntax.Tm_app (uu____3766))
in (FStar_Syntax_Syntax.mk uu____3765))
in (uu____3762 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____3803 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3810) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____3817) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____3803) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____3830 -> c0)}
end)))


let mk_forall_aux = (fun fa x body -> (

let uu____3854 = (

let uu____3857 = (

let uu____3858 = (

let uu____3868 = (

let uu____3870 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____3871 = (

let uu____3873 = (

let uu____3874 = (

let uu____3875 = (

let uu____3876 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3876)::[])
in (

let uu____3877 = (

let uu____3884 = (

let uu____3890 = (

let uu____3891 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp uu____3891))
in FStar_Util.Inl (uu____3890))
in FStar_Pervasives_Native.Some (uu____3884))
in (abs uu____3875 body uu____3877)))
in (FStar_Syntax_Syntax.as_arg uu____3874))
in (uu____3873)::[])
in (uu____3870)::uu____3871))
in ((fa), (uu____3868)))
in FStar_Syntax_Syntax.Tm_app (uu____3858))
in (FStar_Syntax_Syntax.mk uu____3857))
in (uu____3854 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____3941 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____3941) with
| true -> begin
f1
end
| uu____3942 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____3954) -> begin
true
end
| uu____3955 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (

let uu____3998 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((uu____3998), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____4021 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((uu____4021), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____4033 = (

let uu____4034 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4034))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____4033)))))


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
| uu____4110 -> begin
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
| uu____4134 -> begin
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
| uu____4157 -> begin
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
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____4182)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____4192)) -> begin
(unmeta_monadic t)
end
| uu____4202 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let rec aux = (fun f2 uu____4247 -> (match (uu____4247) with
| (lid, arity) -> begin
(

let uu____4253 = (

let uu____4263 = (unmeta_monadic f2)
in (head_and_args uu____4263))
in (match (uu____4253) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____4282 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____4282) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____4297 -> begin
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

let uu____4333 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____4333)))
end
| uu____4340 -> begin
(

let uu____4341 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____4341)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4369 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____4383 = (head_and_args t1)
in (match (uu____4383) with
| (t2, args) -> begin
(

let uu____4414 = (un_uinst t2)
in (

let uu____4415 = (FStar_All.pipe_right args (FStar_List.map (fun uu____4431 -> (match (uu____4431) with
| (t3, imp) -> begin
(

let uu____4438 = (unascribe t3)
in ((uu____4438), (imp)))
end))))
in ((uu____4414), (uu____4415))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____4461 = (

let uu____4470 = (flat t1)
in ((qopt), (uu____4470)))
in (match (uu____4461) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____4485; FStar_Syntax_Syntax.pos = uu____4486; FStar_Syntax_Syntax.vars = uu____4487}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____4490); FStar_Syntax_Syntax.tk = uu____4491; FStar_Syntax_Syntax.pos = uu____4492; FStar_Syntax_Syntax.vars = uu____4493}, uu____4494))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____4555; FStar_Syntax_Syntax.pos = uu____4556; FStar_Syntax_Syntax.vars = uu____4557}, (uu____4558)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____4561); FStar_Syntax_Syntax.tk = uu____4562; FStar_Syntax_Syntax.pos = uu____4563; FStar_Syntax_Syntax.vars = uu____4564}, uu____4565))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____4633; FStar_Syntax_Syntax.pos = uu____4634; FStar_Syntax_Syntax.vars = uu____4635}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____4638); FStar_Syntax_Syntax.tk = uu____4639; FStar_Syntax_Syntax.pos = uu____4640; FStar_Syntax_Syntax.vars = uu____4641}, uu____4642))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = uu____4710; FStar_Syntax_Syntax.pos = uu____4711; FStar_Syntax_Syntax.vars = uu____4712}, (uu____4713)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____4716); FStar_Syntax_Syntax.tk = uu____4717; FStar_Syntax_Syntax.pos = uu____4718; FStar_Syntax_Syntax.vars = uu____4719}, uu____4720))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (b), uu____4796) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____4814 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4814) with
| (bs1, t2) -> begin
(

let uu____4820 = (patterns t2)
in (match (uu____4820) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____4851 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____4858 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let phi = (unmeta_monadic f)
in (

let uu____4870 = (destruct_base_conn phi)
in (match (uu____4870) with
| FStar_Pervasives_Native.Some (b) -> begin
FStar_Pervasives_Native.Some (b)
end
| FStar_Pervasives_Native.None -> begin
(destruct_q_conn phi)
end))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____4881 = (

let uu____4884 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____4884))
in (

let uu____4885 = (

let uu____4886 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____4886))
in (

let uu____4889 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____4881 a.FStar_Syntax_Syntax.action_univs uu____4885 FStar_Parser_Const.effect_Tot_lid uu____4889))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]), ([]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta}))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____4922 = (

let uu____4925 = (

let uu____4926 = (

let uu____4936 = (

let uu____4938 = (FStar_Syntax_Syntax.as_arg t)
in (uu____4938)::[])
in ((reify_), (uu____4936)))
in FStar_Syntax_Syntax.Tm_app (uu____4926))
in (FStar_Syntax_Syntax.mk uu____4925))
in (uu____4922 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4954) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____4976) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____4977) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____4978) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____4994) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____5003) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____5004) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____5005) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____5014) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____5019; FStar_Syntax_Syntax.index = uu____5020; FStar_Syntax_Syntax.sort = t2}, uu____5022) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____5030) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5036, uu____5037) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____5067) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____5082, t2, uu____5084) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____5107, t2) -> begin
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

let uu____5127 = (delta_qualifier t)
in (incr_delta_depth uu____5127)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5131 = (

let uu____5132 = (FStar_Syntax_Subst.compress t)
in uu____5132.FStar_Syntax_Syntax.n)
in (match (uu____5131) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____5135 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____5143 = (

let uu____5153 = (unmeta e)
in (head_and_args uu____5153))
in (match (uu____5143) with
| (head1, args) -> begin
(

let uu____5172 = (

let uu____5180 = (

let uu____5181 = (un_uinst head1)
in uu____5181.FStar_Syntax_Syntax.n)
in ((uu____5180), (args)))
in (match (uu____5172) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____5192) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5205)::((hd1, uu____5207))::((tl1, uu____5209))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____5243 = (

let uu____5247 = (

let uu____5251 = (list_elements tl1)
in (FStar_Util.must uu____5251))
in (hd1)::uu____5247)
in FStar_Pervasives_Native.Some (uu____5243))
end
| uu____5260 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____5291 = (f a)
in (uu____5291)::[])
end
| (x)::xs -> begin
(

let uu____5295 = (apply_last f xs)
in (x)::uu____5295)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____5325 = (

let uu____5328 = (

let uu____5329 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____5329))
in (FStar_Syntax_Syntax.mk uu____5328))
in (uu____5325 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____5347 = (

let uu____5348 = (

let uu____5349 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5349 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5348 args))
in (uu____5347 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____5363 = (

let uu____5364 = (

let uu____5365 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5365 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____5364 args))
in (uu____5363 FStar_Pervasives_Native.None pos)))
in (

let uu____5370 = (

let uu____5371 = (

let uu____5372 = (FStar_Syntax_Syntax.iarg typ)
in (uu____5372)::[])
in (nil uu____5371 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____5375 = (

let uu____5376 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____5377 = (

let uu____5379 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____5380 = (

let uu____5382 = (FStar_Syntax_Syntax.as_arg a)
in (uu____5382)::[])
in (uu____5379)::uu____5380))
in (uu____5376)::uu____5377))
in (cons1 uu____5375 t.FStar_Syntax_Syntax.pos))) l uu____5370))))))


let rec eqlist = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____5426 -> begin
false
end))


let eqsum = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____5499 -> begin
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
| uu____5607 -> begin
false
end))


let rec term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let uu____5700 = (

let uu____5703 = (

let uu____5704 = (FStar_Syntax_Subst.compress t1)
in uu____5704.FStar_Syntax_Syntax.n)
in (

let uu____5707 = (

let uu____5708 = (FStar_Syntax_Subst.compress t2)
in uu____5708.FStar_Syntax_Syntax.n)
in ((uu____5703), (uu____5707))))
in (match (uu____5700) with
| (FStar_Syntax_Syntax.Tm_bvar (x), FStar_Syntax_Syntax.Tm_bvar (y)) -> begin
(x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_fvar (x), FStar_Syntax_Syntax.Tm_fvar (y)) -> begin
(FStar_Syntax_Syntax.fv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_constant (x), FStar_Syntax_Syntax.Tm_constant (y)) -> begin
(x = y)
end
| (FStar_Syntax_Syntax.Tm_type (x), FStar_Syntax_Syntax.Tm_type (y)) -> begin
(x = y)
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t11, k1), FStar_Syntax_Syntax.Tm_abs (b2, t21, k2)) -> begin
((eqlist binder_eq b1 b2) && (term_eq t11 t21))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((term_eq f1 f2) && (eqlist arg_eq a1 a2))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((eqlist binder_eq b1 b2) && (comp_eq c1 c2))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t11), FStar_Syntax_Syntax.Tm_refine (b2, t21)) -> begin
((FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t11 t21))
end
| (FStar_Syntax_Syntax.Tm_match (t11, bs1), FStar_Syntax_Syntax.Tm_match (t21, bs2)) -> begin
((term_eq t11 t21) && (eqlist branch_eq bs1 bs2))
end
| (uu____5913, uu____5914) -> begin
false
end)))
and arg_eq : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun a1 a2 -> (eqprod term_eq (fun q1 q2 -> (q1 = q2)) a1 a2))
and binder_eq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun b1 b2 -> (eqprod (fun b11 b21 -> (term_eq b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)) (fun q1 q2 -> (q1 = q2)) b1 b2))
and lcomp_eq = (fun c1 c2 -> false)
and residual_eq = (fun r1 r2 -> false)
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
| (uu____5985, uu____5986) -> begin
false
end))
and eq_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  Prims.bool = (fun f1 f2 -> false)
and branch_eq : ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun uu____5991 uu____5992 -> (match (((uu____5991), (uu____5992))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
false
end))


let rec bottom_fold : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun f t -> (

let ff = (bottom_fold f)
in (

let tn = (

let uu____6102 = (un_uinst t)
in uu____6102.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (f1, args) -> begin
(

let uu____6122 = (

let uu____6132 = (ff f1)
in (

let uu____6133 = (FStar_List.map (fun uu____6141 -> (match (uu____6141) with
| (a, q) -> begin
(

let uu____6148 = (ff a)
in ((uu____6148), (q)))
end)) args)
in ((uu____6132), (uu____6133))))
in FStar_Syntax_Syntax.Tm_app (uu____6122))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____6177 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____6177) with
| (bs1, t') -> begin
(

let t'' = (ff t')
in (

let uu____6183 = (

let uu____6198 = (FStar_Syntax_Subst.close bs1 t'')
in ((bs1), (uu____6198), (k)))
in FStar_Syntax_Syntax.Tm_abs (uu____6183)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
tn
end
| uu____6217 -> begin
tn
end)
in (f (

let uu___168_6218 = t
in {FStar_Syntax_Syntax.n = tn1; FStar_Syntax_Syntax.tk = uu___168_6218.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___168_6218.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___168_6218.FStar_Syntax_Syntax.vars}))))))




