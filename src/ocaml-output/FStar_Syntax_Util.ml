
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

let uu___173_639 = c
in (

let uu____640 = (

let uu____641 = (

let uu___174_642 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___174_642.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___174_642.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___174_642.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___174_642.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____641))
in {FStar_Syntax_Syntax.n = uu____640; FStar_Syntax_Syntax.tk = uu___173_639.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___173_639.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___173_639.FStar_Syntax_Syntax.vars}))))


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


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___161_704 -> (match (uu___161_704) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____705 -> begin
false
end)))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___162_710 -> (match (uu___162_710) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____711 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___163_716 -> (match (uu___163_716) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____717 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___164_730 -> (match (uu___164_730) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| uu____731 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___165_736 -> (match (uu___165_736) with
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
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___166_777 -> (match (uu___166_777) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____778 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___167_797 -> (match (uu___167_797) with
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
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___168_1018 -> (match (uu___168_1018) with
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

let uu___175_1077 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___175_1077.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___175_1077.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___175_1077.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___175_1077.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___169_1090 -> (match (uu___169_1090) with
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

let equal_if = (fun uu___170_1271 -> (match (uu___170_1271) with
| true -> begin
Equal
end
| uu____1272 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___171_1276 -> (match (uu___171_1276) with
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


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_let (_, lids, _, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _)) -> begin
(lid)::[]
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (n1)) | (FStar_Syntax_Syntax.Sig_new_effect (n1)) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| uu____1792 -> begin
None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_bundle (_, quals, _)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, quals)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals)) | (FStar_Syntax_Syntax.Sig_assume (_, _, quals)) | (FStar_Syntax_Syntax.Sig_let (_, _, quals, _)) | (FStar_Syntax_Syntax.Sig_new_effect ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _})) | (FStar_Syntax_Syntax.Sig_new_effect_for_free ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _})) -> begin
quals
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb = (fun uu___172_1908 -> (match (uu___172_1908) with
| (FStar_Util.Inl (x), uu____1915, uu____1916) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____1920, uu____1921) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun uu____1938 -> (match (uu____1938) with
| (hd1, uu____1944) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(

let uu____2058 = (

let uu____2061 = (

let uu____2062 = (

let uu____2067 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2067), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____2062))
in (FStar_Syntax_Syntax.mk uu____2061))
in (uu____2058 None (FStar_Ident.range_of_lid l)))
end
| uu____2076 -> begin
(

let e = (

let uu____2085 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____2085 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "^fname^")) with
| true -> begin
(

let uu____2100 = (

let uu____2103 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((uu____2103), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2100))
end
| uu____2104 -> begin
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
| uu____2123 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____2136 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2136) with
| true -> begin
(

let uu____2137 = (

let uu____2140 = (

let uu____2141 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____2141))
in (

let uu____2142 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____2140), (uu____2142))))
in (FStar_Ident.mk_ident uu____2137))
end
| uu____2143 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___176_2145 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___176_2145.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___176_2145.FStar_Syntax_Syntax.sort})
in (

let uu____2146 = (mk_field_projector_name_from_ident lid nm)
in ((uu____2146), (y))))))


let set_uvar = (fun uv t -> (

let uu____2163 = (FStar_Unionfind.find uv)
in (match (uu____2163) with
| FStar_Syntax_Syntax.Fixed (uu____2166) -> begin
(

let uu____2167 = (

let uu____2168 = (

let uu____2169 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2169))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2168))
in (failwith uu____2167))
end
| uu____2171 -> begin
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
| uu____2218 -> begin
(q1 = q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt1
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____2293 = (

let uu____2299 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (uu____2299))
in Some (uu____2293))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____2310 -> begin
(

let body = (

let uu____2312 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____2312))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), None) -> begin
(

let uu____2355 = (

let uu____2358 = (

let uu____2359 = (

let uu____2374 = (

let uu____2378 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____2378 bs'))
in (

let uu____2384 = (close_lopt lopt')
in ((uu____2374), (t1), (uu____2384))))
in FStar_Syntax_Syntax.Tm_abs (uu____2359))
in (FStar_Syntax_Syntax.mk uu____2358))
in (uu____2355 None t1.FStar_Syntax_Syntax.pos))
end
| uu____2410 -> begin
(

let uu____2419 = (

let uu____2422 = (

let uu____2423 = (

let uu____2438 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2439 = (close_lopt lopt)
in ((uu____2438), (body), (uu____2439))))
in FStar_Syntax_Syntax.Tm_abs (uu____2423))
in (FStar_Syntax_Syntax.mk uu____2422))
in (uu____2419 None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____2482 -> begin
(

let uu____2486 = (

let uu____2489 = (

let uu____2490 = (

let uu____2498 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____2499 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____2498), (uu____2499))))
in FStar_Syntax_Syntax.Tm_arrow (uu____2490))
in (FStar_Syntax_Syntax.mk uu____2489))
in (uu____2486 None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____2529 = (

let uu____2530 = (FStar_Syntax_Subst.compress t)
in uu____2530.FStar_Syntax_Syntax.n)
in (match (uu____2529) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____2550) -> begin
(

let uu____2557 = (

let uu____2558 = (FStar_Syntax_Subst.compress tres)
in uu____2558.FStar_Syntax_Syntax.n)
in (match (uu____2557) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(

let uu____2575 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c'))))) uu____2575 t.FStar_Syntax_Syntax.pos))
end
| uu____2595 -> begin
t
end))
end
| uu____2596 -> begin
t
end)
end
| uu____2597 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____2606 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (

let uu____2611 = (

let uu____2612 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____2612 t.FStar_Syntax_Syntax.pos))
in (

let uu____2613 = (

let uu____2616 = (

let uu____2617 = (

let uu____2622 = (

let uu____2623 = (

let uu____2624 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2624)::[])
in (FStar_Syntax_Subst.close uu____2623 t))
in ((b), (uu____2622)))
in FStar_Syntax_Syntax.Tm_refine (uu____2617))
in (FStar_Syntax_Syntax.mk uu____2616))
in (uu____2613 uu____2606 uu____2611)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2662 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2662) with
| (bs1, c1) -> begin
(

let uu____2672 = (is_tot_or_gtot_comp c1)
in (match (uu____2672) with
| true -> begin
(

let uu____2678 = (arrow_formals_comp (comp_result c1))
in (match (uu____2678) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____2702 -> begin
((bs1), (c1))
end))
end))
end
| uu____2703 -> begin
(

let uu____2704 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____2704)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____2720 = (arrow_formals_comp k)
in (match (uu____2720) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l1)) -> begin
(

let l2 = (

let uu___177_2801 = l1
in (

let uu____2802 = (FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___177_2801.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____2802; FStar_Syntax_Syntax.cflags = uu___177_2801.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2805 -> (

let uu____2806 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____2806)))}))
in Some (FStar_Util.Inl (l2)))
end
| uu____2815 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____2853 = (

let uu____2854 = (

let uu____2857 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____2857))
in uu____2854.FStar_Syntax_Syntax.n)
in (match (uu____2853) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____2895 = (aux t2 what)
in (match (uu____2895) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____2952 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____2964 = (aux t None)
in (match (uu____2964) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____3012 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____3012) with
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
| (Some (fvs), uu____3112) -> begin
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

let uu____3173 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____3173) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____3189 -> begin
(

let t' = (arrow binders c)
in (

let uu____3196 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____3196) with
| (uvs1, t'1) -> begin
(

let uu____3207 = (

let uu____3208 = (FStar_Syntax_Subst.compress t'1)
in uu____3208.FStar_Syntax_Syntax.n)
in (match (uu____3207) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____3234 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| uu____3249 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3257 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "tuple%s" uu____3257))
in (

let uu____3258 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3258 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3266 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "Mktuple%s" uu____3266))
in (

let uu____3267 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3267 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n1 -> (

let uu____3274 = (mk_tuple_data_lid n1 FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f uu____3274)))


let is_tuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> ((f.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with f.FStar_Ident.ident.FStar_Ident.idText "Mktuple")))


let is_tuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"))


let is_dtuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((lid.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText "Prims.dtuple")))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____3292 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3300 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "dtuple%s" uu____3300))
in (

let uu____3301 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3301 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 r -> (

let t = (

let uu____3309 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "Mkdtuple%s" uu____3309))
in (

let uu____3310 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range uu____3310 r))))


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

let uu____3348 = (

let uu____3349 = (pre_typ t)
in uu____3349.FStar_Syntax_Syntax.n)
in (match (uu____3348) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____3357 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3364 = (

let uu____3365 = (pre_typ t)
in uu____3365.FStar_Syntax_Syntax.n)
in (match (uu____3364) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3368) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____3370) -> begin
(is_constructed_typ t1 lid)
end
| uu____3385 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____3396) -> begin
(get_tycon t2)
end
| uu____3411 -> begin
None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero))) None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____3441 -> (

let u = (

let uu____3445 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _0_26 -> FStar_Syntax_Syntax.U_unif (_0_26)) uu____3445))
in (

let uu____3451 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None FStar_Range.dummyRange)
in ((uu____3451), (u)))))


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

let uu____3478 = (

let uu____3481 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3482 = (

let uu____3485 = (

let uu____3486 = (

let uu____3496 = (

let uu____3498 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____3499 = (

let uu____3501 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3501)::[])
in (uu____3498)::uu____3499))
in ((tand), (uu____3496)))
in FStar_Syntax_Syntax.Tm_app (uu____3486))
in (FStar_Syntax_Syntax.mk uu____3485))
in (uu____3482 None uu____3481)))
in Some (uu____3478))
end))


let mk_binop = (fun op_t phi1 phi2 -> (

let uu____3536 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____3537 = (

let uu____3540 = (

let uu____3541 = (

let uu____3551 = (

let uu____3553 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____3554 = (

let uu____3556 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____3556)::[])
in (uu____3553)::uu____3554))
in ((op_t), (uu____3551)))
in FStar_Syntax_Syntax.Tm_app (uu____3541))
in (FStar_Syntax_Syntax.mk uu____3540))
in (uu____3537 None uu____3536))))


let mk_neg = (fun phi -> (

let uu____3577 = (

let uu____3580 = (

let uu____3581 = (

let uu____3591 = (

let uu____3593 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____3593)::[])
in ((t_not), (uu____3591)))
in FStar_Syntax_Syntax.Tm_app (uu____3581))
in (FStar_Syntax_Syntax.mk uu____3580))
in (uu____3577 None phi.FStar_Syntax_Syntax.pos)))


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

let uu____3653 = (

let uu____3654 = (FStar_Syntax_Subst.compress phi1)
in uu____3654.FStar_Syntax_Syntax.n)
in (match (uu____3653) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| uu____3659 -> begin
(

let uu____3660 = (

let uu____3661 = (FStar_Syntax_Subst.compress phi2)
in uu____3661.FStar_Syntax_Syntax.n)
in (match (uu____3660) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| uu____3665 -> begin
(mk_binop timp phi1 phi2)
end))
end)))


let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t = (fun e -> (

let uu____3689 = (

let uu____3692 = (

let uu____3693 = (

let uu____3703 = (

let uu____3705 = (FStar_Syntax_Syntax.as_arg e)
in (uu____3705)::[])
in ((b2t_v), (uu____3703)))
in FStar_Syntax_Syntax.Tm_app (uu____3693))
in (FStar_Syntax_Syntax.mk uu____3692))
in (uu____3689 None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)


let mk_untyped_eq2 = (fun e1 e2 -> (

let uu____3729 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3730 = (

let uu____3733 = (

let uu____3734 = (

let uu____3744 = (

let uu____3746 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3747 = (

let uu____3749 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3749)::[])
in (uu____3746)::uu____3747))
in ((teq), (uu____3744)))
in FStar_Syntax_Syntax.Tm_app (uu____3734))
in (FStar_Syntax_Syntax.mk uu____3733))
in (uu____3730 None uu____3729))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____3772 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____3773 = (

let uu____3776 = (

let uu____3777 = (

let uu____3787 = (

let uu____3789 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3790 = (

let uu____3792 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____3793 = (

let uu____3795 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____3795)::[])
in (uu____3792)::uu____3793))
in (uu____3789)::uu____3790))
in ((eq_inst), (uu____3787)))
in FStar_Syntax_Syntax.Tm_app (uu____3777))
in (FStar_Syntax_Syntax.mk uu____3776))
in (uu____3773 None uu____3772)))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) None FStar_Range.dummyRange)
in (

let uu____3833 = (

let uu____3836 = (

let uu____3837 = (

let uu____3847 = (

let uu____3849 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____3850 = (

let uu____3852 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____3853 = (

let uu____3855 = (FStar_Syntax_Syntax.as_arg t')
in (uu____3855)::[])
in (uu____3852)::uu____3853))
in (uu____3849)::uu____3850))
in ((t_has_type1), (uu____3847)))
in FStar_Syntax_Syntax.Tm_app (uu____3837))
in (FStar_Syntax_Syntax.mk uu____3836))
in (uu____3833 None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____3874 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3881) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____3888) -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____3874) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____3901 -> c0)}
end)))


let mk_forall_aux = (fun fa x body -> (

let uu____3925 = (

let uu____3928 = (

let uu____3929 = (

let uu____3939 = (

let uu____3941 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____3942 = (

let uu____3944 = (

let uu____3945 = (

let uu____3946 = (

let uu____3947 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____3947)::[])
in (

let uu____3948 = (

let uu____3955 = (

let uu____3961 = (

let uu____3962 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp uu____3962))
in FStar_Util.Inl (uu____3961))
in Some (uu____3955))
in (abs uu____3946 body uu____3948)))
in (FStar_Syntax_Syntax.as_arg uu____3945))
in (uu____3944)::[])
in (uu____3941)::uu____3942))
in ((fa), (uu____3939)))
in FStar_Syntax_Syntax.Tm_app (uu____3929))
in (FStar_Syntax_Syntax.mk uu____3928))
in (uu____3925 None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____4012 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____4012) with
| true -> begin
f1
end
| uu____4013 -> begin
(mk_forall_no_univ (Prims.fst b) f1)
end))) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____4025) -> begin
true
end
| uu____4026 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (

let uu____4069 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((uu____4069), (None), (t1)))
in (

let else_branch = (

let uu____4092 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((uu____4092), (None), (t2)))
in (

let uu____4104 = (

let uu____4105 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4105))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None uu____4104)))))


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
| uu____4178 -> begin
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
| uu____4202 -> begin
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
| uu____4225 -> begin
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
| uu____4260 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Syntax_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let rec aux = (fun f2 uu____4305 -> (match (uu____4305) with
| (lid, arity) -> begin
(

let uu____4311 = (

let uu____4321 = (unmeta_monadic f2)
in (head_and_args uu____4321))
in (match (uu____4311) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____4340 = ((is_constructor t1 lid) && ((FStar_List.length args) = arity))
in (match (uu____4340) with
| true -> begin
Some (BaseConn (((lid), (args))))
end
| uu____4355 -> begin
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

let uu____4391 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____4391)))
end
| uu____4398 -> begin
(

let uu____4399 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____4399)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4427 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____4441 = (head_and_args t1)
in (match (uu____4441) with
| (t2, args) -> begin
(

let uu____4472 = (un_uinst t2)
in (

let uu____4473 = (FStar_All.pipe_right args (FStar_List.map (fun uu____4489 -> (match (uu____4489) with
| (t3, imp) -> begin
(

let uu____4496 = (unascribe t3)
in ((uu____4496), (imp)))
end))))
in ((uu____4472), (uu____4473))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____4519 = (

let uu____4528 = (flat t1)
in ((qopt), (uu____4528)))
in (match (uu____4519) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), uu____4787) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____4805 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4805) with
| (bs1, t2) -> begin
(

let uu____4811 = (patterns t2)
in (match (uu____4811) with
| (pats, body) -> begin
(match (b) with
| true -> begin
Some (QAll (((bs1), (pats), (body))))
end
| uu____4842 -> begin
Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____4849 -> begin
None
end)))
in (aux None [] t)))))
in (

let phi = (unmeta_monadic f)
in (

let uu____4861 = (destruct_base_conn phi)
in (match (uu____4861) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____4872 = (

let uu____4875 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (uu____4875))
in (

let uu____4876 = (

let uu____4877 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____4877))
in (

let uu____4880 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn None)
in (close_univs_and_mk_letbinding None uu____4872 a.FStar_Syntax_Syntax.action_univs uu____4876 FStar_Syntax_Const.effect_Tot_lid uu____4880))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]), ((FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]), ([]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos}))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) None t.FStar_Syntax_Syntax.pos)
in (

let uu____4914 = (

let uu____4917 = (

let uu____4918 = (

let uu____4928 = (

let uu____4930 = (FStar_Syntax_Syntax.as_arg t)
in (uu____4930)::[])
in ((reify_), (uu____4928)))
in FStar_Syntax_Syntax.Tm_app (uu____4918))
in (FStar_Syntax_Syntax.mk uu____4917))
in (uu____4914 None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4946) -> begin
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

let uu____5057 = (

let uu____5058 = (FStar_Syntax_Subst.compress t)
in uu____5058.FStar_Syntax_Syntax.n)
in (match (uu____5057) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____5061 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list Prims.option = (fun e -> (

let uu____5069 = (

let uu____5079 = (unmeta e)
in (head_and_args uu____5079))
in (match (uu____5069) with
| (head1, args) -> begin
(

let uu____5098 = (

let uu____5106 = (

let uu____5107 = (un_uinst head1)
in uu____5107.FStar_Syntax_Syntax.n)
in ((uu____5106), (args)))
in (match (uu____5098) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____5118) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5131)::((hd1, uu____5133))::((tl1, uu____5135))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(

let uu____5169 = (

let uu____5173 = (

let uu____5177 = (list_elements tl1)
in (FStar_Util.must uu____5177))
in (hd1)::uu____5173)
in Some (uu____5169))
end
| uu____5186 -> begin
None
end))
end)))




