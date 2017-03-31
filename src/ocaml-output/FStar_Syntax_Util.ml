
open Prims

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

let uu____96 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in ((uu____96), ((Prims.snd b))))
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
in (uu____183 None t.FStar_Syntax_Syntax.pos))
end
| uu____212 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____232 -> (match (uu____232) with
| (t, imp) -> begin
(

let uu____239 = (

let uu____240 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst uu____240))
in ((uu____239), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____266 -> (match (uu____266) with
| (t, imp) -> begin
(

let uu____279 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____279), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____286 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____286 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((Prims.fst f)), ((Prims.fst a)))))::out) formals actuals [])
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
| (FStar_Syntax_Syntax.Tm_meta (e2, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e2, _, _)) -> begin
(unmeta e2)
end
| uu____407 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____418 = (univ_kernel u1)
in (match (uu____418) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____425) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____429) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____435 = (univ_kernel u)
in (Prims.snd uu____435)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____448) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____449, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____450) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____451, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____454), FStar_Syntax_Syntax.U_unif (uu____455)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____458), FStar_Syntax_Syntax.U_name (uu____459)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____468 = (FStar_Unionfind.uvar_id u11)
in (

let uu____470 = (FStar_Unionfind.uvar_id u21)
in (uu____468 - uu____470)))
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
| uu____489 -> begin
(

let copt = (

let uu____492 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____492 (fun uu____498 -> (match (uu____498) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((c <> (Prims.parse_int "0"))) with
| true -> begin
Some (c)
end
| uu____506 -> begin
None
end))
end))))
in (match (copt) with
| None -> begin
(Prims.parse_int "0")
end
| Some (c) -> begin
c
end))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____508), uu____509) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____511, FStar_Syntax_Syntax.U_max (uu____512)) -> begin
(Prims.parse_int "1")
end
| uu____514 -> begin
(

let uu____517 = (univ_kernel u1)
in (match (uu____517) with
| (k1, n1) -> begin
(

let uu____522 = (univ_kernel u2)
in (match (uu____522) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((r = (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____528 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____535 = (compare_univs u1 u2)
in (uu____535 = (Prims.parse_int "0"))))


let ml_comp : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____562) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____568) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____586) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____592) -> begin
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
| (FStar_Syntax_Syntax.Total (t, u_opt)) | (FStar_Syntax_Syntax.GTotal (t, u_opt)) -> begin
(

let uu____628 = (

let uu____629 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____629))
in {FStar_Syntax_Syntax.comp_univs = uu____628; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end))
in (

let uu___177_639 = c
in (

let uu____640 = (

let uu____641 = (

let uu___178_642 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___178_642.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___178_642.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___178_642.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___178_642.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____641))
in {FStar_Syntax_Syntax.n = uu____640; FStar_Syntax_Syntax.tk = uu___177_639.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___177_639.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___177_639.FStar_Syntax_Syntax.vars}))))


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1
end
| (FStar_Syntax_Syntax.Total (t, Some (u))) | (FStar_Syntax_Syntax.GTotal (t, Some (u))) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| uu____667 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____680) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____686) -> begin
false
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___165_704 -> (match (uu___165_704) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____705 -> begin
false
end)))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___166_710 -> (match (uu___166_710) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____711 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___167_716 -> (match (uu___167_716) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____717 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___168_730 -> (match (uu___168_730) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| uu____731 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___169_736 -> (match (uu___169_736) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| uu____737 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____763) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____769) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___170_777 -> (match (uu___170_777) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____778 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___171_797 -> (match (uu___171_797) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____798 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____805 = (

let uu____806 = (FStar_Syntax_Subst.compress t)
in uu____806.FStar_Syntax_Syntax.n)
in (match (uu____805) with
| FStar_Syntax_Syntax.Tm_arrow (uu____809, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____821 -> begin
true
end)))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____825 = (

let uu____826 = (FStar_Syntax_Subst.compress t)
in uu____826.FStar_Syntax_Syntax.n)
in (match (uu____825) with
| FStar_Syntax_Syntax.Tm_arrow (uu____829, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| uu____842 -> begin
false
end)
end
| uu____843 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____889 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____904) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____909 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____913 = (

let uu____914 = (FStar_Syntax_Subst.compress t)
in uu____914.FStar_Syntax_Syntax.n)
in (match (uu____913) with
| FStar_Syntax_Syntax.Tm_arrow (uu____917, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____933))::uu____934 -> begin
(

let pats' = (unmeta pats)
in (

let uu____965 = (head_and_args pats')
in (match (uu____965) with
| (head1, uu____976) -> begin
(

let uu____991 = (

let uu____992 = (un_uinst head1)
in uu____992.FStar_Syntax_Syntax.n)
in (match (uu____991) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| uu____996 -> begin
false
end))
end)))
end
| uu____997 -> begin
false
end)
end
| uu____1003 -> begin
false
end)
end
| uu____1004 -> begin
false
end)))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___172_1018 -> (match (uu___172_1018) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1019 -> begin
false
end)))))
end
| uu____1020 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t, _)) | (FStar_Syntax_Syntax.GTotal (t, _)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1064) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1070) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___179_1077 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___179_1077.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___179_1077.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___179_1077.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___179_1077.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___173_1090 -> (match (uu___173_1090) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____1091 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____1113 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1119, uu____1120) -> begin
(unascribe e2)
end
| uu____1149 -> begin
e1
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1191, uu____1192) -> begin
(ascribe t' k)
end
| uu____1221 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (None)))) None t.FStar_Syntax_Syntax.pos)
end))

type eq_result =
| Equal
| NotEqual
| Unknown


let uu___is_Equal : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equal -> begin
true
end
| uu____1243 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1247 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1251 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t11 = (unascribe t1)
in (

let t21 = (unascribe t2)
in (

let equal_if = (fun uu___174_1271 -> (match (uu___174_1271) with
| true -> begin
Equal
end
| uu____1272 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___175_1276 -> (match (uu___175_1276) with
| true -> begin
Equal
end
| uu____1277 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____1290 -> begin
Unknown
end))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(

let uu____1295 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____1295))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____1308 = (eq_tm f g)
in (eq_and uu____1308 (fun uu____1309 -> (

let uu____1310 = (eq_univs_list us vs)
in (equal_if uu____1310)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____1313 = (FStar_Const.eq_const c d)
in (equal_iff uu____1313))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____1315), FStar_Syntax_Syntax.Tm_uvar (u2, uu____1317)) -> begin
(

let uu____1342 = (FStar_Unionfind.equivalent u1 u2)
in (equal_if uu____1342))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____1378 = (eq_tm h1 h2)
in (eq_and uu____1378 (fun uu____1379 -> (eq_args args1 args2))))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____1382 = (eq_univs u v1)
in (equal_if uu____1382))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____1384), uu____1385) -> begin
(eq_tm t12 t21)
end
| (uu____1390, FStar_Syntax_Syntax.Tm_meta (t22, uu____1392)) -> begin
(eq_tm t11 t22)
end
| uu____1397 -> begin
Unknown
end)))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____1421))::a11, ((b, uu____1424))::b1) -> begin
(

let uu____1462 = (eq_tm a b)
in (match (uu____1462) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____1463 -> begin
Unknown
end))
end
| uu____1464 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____1478) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1484, uu____1485) -> begin
(unrefine t2)
end
| uu____1514 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1518 = (

let uu____1519 = (unrefine t)
in uu____1519.FStar_Syntax_Syntax.n)
in (match (uu____1518) with
| FStar_Syntax_Syntax.Tm_type (uu____1522) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1525) -> begin
(is_unit t1)
end
| uu____1530 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1534 = (

let uu____1535 = (unrefine t)
in uu____1535.FStar_Syntax_Syntax.n)
in (match (uu____1534) with
| FStar_Syntax_Syntax.Tm_type (uu____1538) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____1541) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____1557) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1562, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____1574 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____1578 = (

let uu____1579 = (FStar_Syntax_Subst.compress e)
in uu____1579.FStar_Syntax_Syntax.n)
in (match (uu____1578) with
| FStar_Syntax_Syntax.Tm_abs (uu____1582) -> begin
true
end
| uu____1597 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1601 = (

let uu____1602 = (FStar_Syntax_Subst.compress t)
in uu____1602.FStar_Syntax_Syntax.n)
in (match (uu____1601) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1605) -> begin
true
end
| uu____1613 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____1619) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____1625, uu____1626) -> begin
(pre_typ t2)
end
| uu____1655 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____1669 = (

let uu____1670 = (un_uinst typ1)
in uu____1670.FStar_Syntax_Syntax.n)
in (match (uu____1669) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| uu____1708 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| uu____1724 -> begin
None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (n1, _)) | (FStar_Syntax_Syntax.Sig_new_effect (n1, _)) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| uu____1801 -> begin
None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, quals, _, _)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, quals, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, quals, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_assume (_, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_new_effect ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) -> begin
quals
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_, _)) | (FStar_Syntax_Syntax.Sig_pragma (_, _)) | (FStar_Syntax_Syntax.Sig_main (_, _)) -> begin
[]
end))


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun uu___176_1984 -> (match (uu___176_1984) with
| (FStar_Util.Inl (x), uu____1991, uu____1992) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____1996, uu____1997) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun uu____2014 -> (match (uu____2014) with
| (hd1, uu____2020) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(

let uu____2134 = (

let uu____2137 = (

let uu____2138 = (

let uu____2143 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2143), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____2138))
in (FStar_Syntax_Syntax.mk uu____2137))
in (uu____2134 None (FStar_Ident.range_of_lid l)))
end
| uu____2152 -> begin
(

let e = (

let uu____2161 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____2161 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "^fname^")) with
| true -> begin
(

let uu____2176 = (

let uu____2179 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((uu____2179), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2176))
end
| uu____2180 -> begin
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
| uu____2199 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____2212 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2212) with
| true -> begin
(

let uu____2213 = (

let uu____2216 = (

let uu____2217 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____2217))
in (

let uu____2218 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____2216), (uu____2218))))
in (FStar_Ident.mk_ident uu____2213))
end
| uu____2219 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___180_2221 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___180_2221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___180_2221.FStar_Syntax_Syntax.sort})
in (

let uu____2222 = (mk_field_projector_name_from_ident lid nm)
in ((uu____2222), (y))))))


let set_uvar = (fun uv t -> (

let uu____2239 = (FStar_Unionfind.find uv)
in (match (uu____2239) with
| FStar_Syntax_Syntax.Fixed (uu____2242) -> begin
(

let uu____2243 = (

let uu____2244 = (

let uu____2245 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2245))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2244))
in (failwith uu____2243))
end
| uu____2247 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end)))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText))
end
| ((FStar_Syntax_Syntax.RecordType (ns1, f1), FStar_Syntax_Syntax.RecordType (ns2, f2))) | ((FStar_Syntax_Syntax.RecordConstructor (ns1, f1), FStar_Syntax_Syntax.RecordConstructor (ns2, f2))) -> begin
(((((FStar_List.length ns1) = (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2)) && ((FStar_List.length f1) = (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2))
end
| uu____2294 -> begin
(q1 = q2)
end))


let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (((FStar_List.length bs) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2328 -> begin
(

let close_lopt = (fun lopt1 -> (match (lopt1) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt1
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____2380 = (

let uu____2386 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (uu____2386))
in Some (uu____2380))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____2397 -> begin
(

let body = (

let uu____2402 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____2402))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), None) -> begin
(

let uu____2445 = (

let uu____2448 = (

let uu____2449 = (

let uu____2464 = (

let uu____2468 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____2468 bs'))
in (

let uu____2474 = (close_lopt lopt')
in ((uu____2464), (t1), (uu____2474))))
in FStar_Syntax_Syntax.Tm_abs (uu____2449))
in (FStar_Syntax_Syntax.mk uu____2448))
in (uu____2445 None t1.FStar_Syntax_Syntax.pos))
end
| uu____2500 -> begin
(

let uu____2509 = (

let uu____2512 = (

let uu____2513 = (

let uu____2528 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2529 = (close_lopt lopt)
in ((uu____2528), (body), (uu____2529))))
in FStar_Syntax_Syntax.Tm_abs (uu____2513))
in (FStar_Syntax_Syntax.mk uu____2512))
in (uu____2509 None t.FStar_Syntax_Syntax.pos))
end))
end))
end))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____2572 -> begin
(

let uu____2576 = (

let uu____2579 = (

let uu____2580 = (

let uu____2588 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2589 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____2588), (uu____2589))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2580))
in (FStar_Syntax_Syntax.mk uu____2579))
in (uu____2576 None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____2619 = (

let uu____2620 = (FStar_Syntax_Subst.compress t)
in uu____2620.FStar_Syntax_Syntax.n)
in (match (uu____2619) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____2640) -> begin
(

let uu____2647 = (

let uu____2648 = (FStar_Syntax_Subst.compress tres)
in uu____2648.FStar_Syntax_Syntax.n)
in (match (uu____2647) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(

let uu____2665 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c'))))) uu____2665 t.FStar_Syntax_Syntax.pos))
end
| uu____2685 -> begin
t
end))
end
| uu____2686 -> begin
t
end)
end
| uu____2687 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____2696 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (

let uu____2701 = (

let uu____2702 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____2702 t.FStar_Syntax_Syntax.pos))
in (

let uu____2703 = (

let uu____2706 = (

let uu____2707 = (

let uu____2712 = (

let uu____2713 = (

let uu____2714 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2714)::[])
in (FStar_Syntax_Subst.close uu____2713 t))
in ((b), (uu____2712)))
in FStar_Syntax_Syntax.Tm_refine (uu____2707))
in (FStar_Syntax_Syntax.mk uu____2706))
in (uu____2703 uu____2696 uu____2701)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2752 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2752) with
| (bs1, c1) -> begin
(

let uu____2762 = (is_tot_or_gtot_comp c1)
in (match (uu____2762) with
| true -> begin
(

let uu____2768 = (arrow_formals_comp (comp_result c1))
in (match (uu____2768) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____2792 -> begin
((bs1), (c1))
end))
end))
end
| uu____2793 -> begin
(

let uu____2794 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2794)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____2810 = (arrow_formals_comp k)
in (match (uu____2810) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l1)) -> begin
(

let l2 = (

let uu___181_2891 = l1
in (

let uu____2892 = (FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___181_2891.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2892; FStar_Syntax_Syntax.cflags = uu___181_2891.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2895 -> (

let uu____2896 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____2896)))}))
in Some (FStar_Util.Inl (l2)))
end
| uu____2905 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____2943 = (

let uu____2944 = (

let uu____2947 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____2947))
in uu____2944.FStar_Syntax_Syntax.n)
in (match (uu____2943) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____2985 = (aux t2 what)
in (match (uu____2985) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____3042 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____3054 = (aux t None)
in (match (uu____3054) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____3102 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____3102) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| ((None, _)) | ((_, [])) -> begin
def
end
| (Some (fvs), uu____3202) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_25 -> FStar_Syntax_Syntax.U_name (_0_25))))
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

let uu____3263 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____3263) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____3279 -> begin
(

let t' = (arrow binders c)
in (

let uu____3286 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____3286) with
| (uvs1, t'1) -> begin
(

let uu____3297 = (

let uu____3298 = (FStar_Syntax_Subst.compress t'1)
in uu____3298.FStar_Syntax_Syntax.n)
in (match (uu____3297) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____3324 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| uu____3339 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3347 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "tuple%s" uu____3347))
in (

let uu____3348 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3348 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3356 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "Mktuple%s" uu____3356))
in (

let uu____3357 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3357 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n1 -> (

let uu____3364 = (mk_tuple_data_lid n1 FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f uu____3364)))


let is_tuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> ((f.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with f.FStar_Ident.ident.FStar_Ident.idText "Mktuple")))


let is_tuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"))


let is_dtuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((lid.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText "Prims.dtuple")))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____3382 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3390 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "dtuple%s" uu____3390))
in (

let uu____3391 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3391 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3399 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "Mkdtuple%s" uu____3399))
in (

let uu____3400 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3400 r))))


let is_dtuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> (FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple"))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3438 = (

let uu____3439 = (pre_typ t)
in uu____3439.FStar_Syntax_Syntax.n)
in (match (uu____3438) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____3447 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3454 = (

let uu____3455 = (pre_typ t)
in uu____3455.FStar_Syntax_Syntax.n)
in (match (uu____3454) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3458) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____3460) -> begin
(is_constructed_typ t1 lid)
end
| uu____3475 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3486) -> begin
(get_tycon t2)
end
| uu____3501 -> begin
None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero))) None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____3531 -> (

let u = (

let uu____3535 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _0_26 -> FStar_Syntax_Syntax.U_unif (_0_26)) uu____3535))
in (

let uu____3541 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None FStar_Range.dummyRange)
in ((uu____3541), (u)))))


let kt_kt : FStar_Syntax_Syntax.term = (FStar_Syntax_Const.kunary ktype0 ktype0)


let kt_kt_kt : FStar_Syntax_Syntax.term = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)


let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi11) -> begin
(

let uu____3568 = (

let uu____3571 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3572 = (

let uu____3575 = (

let uu____3576 = (

let uu____3586 = (

let uu____3588 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____3589 = (

let uu____3591 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3591)::[])
in (uu____3588)::uu____3589))
in ((tand), (uu____3586)))
in FStar_Syntax_Syntax.Tm_app (uu____3576))
in (FStar_Syntax_Syntax.mk uu____3575))
in (uu____3572 None uu____3571)))
in Some (uu____3568))
end))


let mk_binop = (fun op_t phi1 phi2 -> (

let uu____3626 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3627 = (

let uu____3630 = (

let uu____3631 = (

let uu____3641 = (

let uu____3643 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____3644 = (

let uu____3646 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3646)::[])
in (uu____3643)::uu____3644))
in ((op_t), (uu____3641)))
in FStar_Syntax_Syntax.Tm_app (uu____3631))
in (FStar_Syntax_Syntax.mk uu____3630))
in (uu____3627 None uu____3626))))


let mk_neg = (fun phi -> (

let uu____3667 = (

let uu____3670 = (

let uu____3671 = (

let uu____3681 = (

let uu____3683 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____3683)::[])
in ((t_not), (uu____3681)))
in FStar_Syntax_Syntax.Tm_app (uu____3671))
in (FStar_Syntax_Syntax.mk uu____3670))
in (uu____3667 None phi.FStar_Syntax_Syntax.pos)))


let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
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


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (

let uu____3743 = (

let uu____3744 = (FStar_Syntax_Subst.compress phi1)
in uu____3744.FStar_Syntax_Syntax.n)
in (match (uu____3743) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| uu____3749 -> begin
(

let uu____3750 = (

let uu____3751 = (FStar_Syntax_Subst.compress phi2)
in uu____3751.FStar_Syntax_Syntax.n)
in (match (uu____3750) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| uu____3755 -> begin
(mk_binop timp phi1 phi2)
end))
end)))


let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t = (fun e -> (

let uu____3779 = (

let uu____3782 = (

let uu____3783 = (

let uu____3793 = (

let uu____3795 = (FStar_Syntax_Syntax.as_arg e)
in (uu____3795)::[])
in ((b2t_v), (uu____3793)))
in FStar_Syntax_Syntax.Tm_app (uu____3783))
in (FStar_Syntax_Syntax.mk uu____3782))
in (uu____3779 None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)


let mk_untyped_eq2 = (fun e1 e2 -> (

let uu____3819 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3820 = (

let uu____3823 = (

let uu____3824 = (

let uu____3834 = (

let uu____3836 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3837 = (

let uu____3839 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3839)::[])
in (uu____3836)::uu____3837))
in ((teq), (uu____3834)))
in FStar_Syntax_Syntax.Tm_app (uu____3824))
in (FStar_Syntax_Syntax.mk uu____3823))
in (uu____3820 None uu____3819))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____3862 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3863 = (

let uu____3866 = (

let uu____3867 = (

let uu____3877 = (

let uu____3879 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3880 = (

let uu____3882 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3883 = (

let uu____3885 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3885)::[])
in (uu____3882)::uu____3883))
in (uu____3879)::uu____3880))
in ((eq_inst), (uu____3877)))
in FStar_Syntax_Syntax.Tm_app (uu____3867))
in (FStar_Syntax_Syntax.mk uu____3866))
in (uu____3863 None uu____3862)))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) None FStar_Range.dummyRange)
in (

let uu____3923 = (

let uu____3926 = (

let uu____3927 = (

let uu____3937 = (

let uu____3939 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3940 = (

let uu____3942 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____3943 = (

let uu____3945 = (FStar_Syntax_Syntax.as_arg t')
in (uu____3945)::[])
in (uu____3942)::uu____3943))
in (uu____3939)::uu____3940))
in ((t_has_type1), (uu____3937)))
in FStar_Syntax_Syntax.Tm_app (uu____3927))
in (FStar_Syntax_Syntax.mk uu____3926))
in (uu____3923 None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____3964 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3971) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____3978) -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____3964) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____3991 -> c0)}
end)))


let mk_forall_aux = (fun fa x body -> (

let uu____4015 = (

let uu____4018 = (

let uu____4019 = (

let uu____4029 = (

let uu____4031 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____4032 = (

let uu____4034 = (

let uu____4035 = (

let uu____4036 = (

let uu____4040 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4040)::[])
in (

let uu____4041 = (

let uu____4048 = (

let uu____4054 = (

let uu____4055 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp uu____4055))
in FStar_Util.Inl (uu____4054))
in Some (uu____4048))
in (abs uu____4036 body uu____4041)))
in (FStar_Syntax_Syntax.as_arg uu____4035))
in (uu____4034)::[])
in (uu____4031)::uu____4032))
in ((fa), (uu____4029)))
in FStar_Syntax_Syntax.Tm_app (uu____4019))
in (FStar_Syntax_Syntax.mk uu____4018))
in (uu____4015 None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____4105 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____4105) with
| true -> begin
f1
end
| uu____4106 -> begin
(mk_forall_no_univ (Prims.fst b) f1)
end))) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____4118) -> begin
true
end
| uu____4119 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (

let uu____4162 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((uu____4162), (None), (t1)))
in (

let else_branch = (

let uu____4185 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((uu____4185), (None), (t2)))
in (

let uu____4197 = (

let uu____4198 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4198))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None uu____4197)))))


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
| uu____4271 -> begin
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
| uu____4295 -> begin
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
| uu____4318 -> begin
false
end))


let __proj__BaseConn__item___0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
_0
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (

let rec unmeta_monadic = (fun f1 -> (

let f2 = (FStar_Syntax_Subst.compress f1)
in (match (f2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_))) | (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (_))) -> begin
(unmeta_monadic t)
end
| uu____4353 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Syntax_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let rec aux = (fun f2 uu____4398 -> (match (uu____4398) with
| (lid, arity) -> begin
(

let uu____4404 = (

let uu____4414 = (unmeta_monadic f2)
in (head_and_args uu____4414))
in (match (uu____4404) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____4433 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____4433) with
| true -> begin
Some (BaseConn (((lid), (args))))
end
| uu____4448 -> begin
None
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

let uu____4484 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____4484)))
end
| uu____4491 -> begin
(

let uu____4492 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____4492)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4520 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____4534 = (head_and_args t1)
in (match (uu____4534) with
| (t2, args) -> begin
(

let uu____4565 = (un_uinst t2)
in (

let uu____4566 = (FStar_All.pipe_right args (FStar_List.map (fun uu____4582 -> (match (uu____4582) with
| (t3, imp) -> begin
(

let uu____4589 = (unascribe t3)
in ((uu____4589), (imp)))
end))))
in ((uu____4565), (uu____4566))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____4612 = (

let uu____4621 = (flat t1)
in ((qopt), (uu____4621)))
in (match (uu____4612) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), uu____4880) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____4898 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4898) with
| (bs1, t2) -> begin
(

let uu____4904 = (patterns t2)
in (match (uu____4904) with
| (pats, body) -> begin
(match (b) with
| true -> begin
Some (QAll (((bs1), (pats), (body))))
end
| uu____4935 -> begin
Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____4942 -> begin
None
end)))
in (aux None [] t)))))
in (

let phi = (unmeta_monadic f)
in (

let uu____4954 = (destruct_base_conn phi)
in (match (uu____4954) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____4965 = (

let uu____4968 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (uu____4968))
in (close_univs_and_mk_letbinding None uu____4965 a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos), ((a.FStar_Syntax_Syntax.action_name)::[]), ((FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]), ([])))))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) None t.FStar_Syntax_Syntax.pos)
in (

let uu____4997 = (

let uu____5000 = (

let uu____5001 = (

let uu____5011 = (

let uu____5013 = (FStar_Syntax_Syntax.as_arg t)
in (uu____5013)::[])
in ((reify_), (uu____5011)))
in FStar_Syntax_Syntax.Tm_app (uu____5001))
in (FStar_Syntax_Syntax.mk uu____5000))
in (uu____4997 None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____5029) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| (FStar_Syntax_Syntax.Tm_uinst (t2, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2}, _)) | (FStar_Syntax_Syntax.Tm_meta (t2, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t2, _, _)) | (FStar_Syntax_Syntax.Tm_app (t2, _)) | (FStar_Syntax_Syntax.Tm_abs (_, t2, _)) | (FStar_Syntax_Syntax.Tm_let (_, t2)) -> begin
(delta_qualifier t2)
end)))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let d = (delta_qualifier t)
in (

let rec aux = (fun d1 -> (match (d1) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d1
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d2) -> begin
(aux d2)
end))
in (aux d))))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____5140 = (

let uu____5141 = (FStar_Syntax_Subst.compress t)
in uu____5141.FStar_Syntax_Syntax.n)
in (match (uu____5140) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____5144 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list Prims.option = (fun e -> (

let uu____5152 = (

let uu____5162 = (unmeta e)
in (head_and_args uu____5162))
in (match (uu____5152) with
| (head1, args) -> begin
(

let uu____5181 = (

let uu____5189 = (

let uu____5190 = (un_uinst head1)
in uu____5190.FStar_Syntax_Syntax.n)
in ((uu____5189), (args)))
in (match (uu____5181) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____5201) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5214)::((hd1, uu____5216))::((tl1, uu____5218))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(

let uu____5252 = (

let uu____5256 = (

let uu____5260 = (list_elements tl1)
in (FStar_Util.must uu____5260))
in (hd1)::uu____5256)
in Some (uu____5252))
end
| uu____5269 -> begin
None
end))
end)))




