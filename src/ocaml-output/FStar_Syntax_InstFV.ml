
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (

let uu____26 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s uu____26 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (mk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____123) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(s t fv)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs = (inst_binders s bs)
in (

let body = (inst s body)
in (

let uu____179 = (

let uu____180 = (

let uu____195 = (inst_lcomp_opt s lopt)
in ((bs), (body), (uu____195)))
in FStar_Syntax_Syntax.Tm_abs (uu____180))
in (mk uu____179))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (inst_binders s bs)
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let uu___158_233 = bv
in (

let uu____234 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___158_233.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_233.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____234}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____254 = (

let uu____255 = (

let uu____265 = (inst s t)
in (

let uu____266 = (inst_args s args)
in ((uu____265), (uu____266))))
in FStar_Syntax_Syntax.Tm_app (uu____255))
in (mk uu____254))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____343 -> (match (uu____343) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____369 = (inst s w)
in Some (uu____369))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (

let uu____374 = (

let uu____375 = (

let uu____391 = (inst s t)
in ((uu____391), (pats)))
in FStar_Syntax_Syntax.Tm_match (uu____375))
in (mk uu____374)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(

let uu____420 = (

let uu____421 = (

let uu____434 = (inst s t1)
in (

let uu____435 = (

let uu____440 = (inst s t2)
in FStar_Util.Inl (uu____440))
in ((uu____434), (uu____435), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____421))
in (mk uu____420))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(

let uu____469 = (

let uu____470 = (

let uu____483 = (inst s t1)
in (

let uu____484 = (

let uu____491 = (inst_comp s c)
in FStar_Util.Inr (uu____491))
in ((uu____483), (uu____484), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____470))
in (mk uu____469))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (

let uu____521 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu___159_527 = lb
in (

let uu____528 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____531 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___159_527.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___159_527.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____528; FStar_Syntax_Syntax.lbeff = uu___159_527.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____531}))))))
in (((Prims.fst lbs)), (uu____521)))
in (

let uu____536 = (

let uu____537 = (

let uu____545 = (inst s t)
in ((lbs), (uu____545)))
in FStar_Syntax_Syntax.Tm_let (uu____537))
in (mk uu____536)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____561 = (

let uu____562 = (

let uu____567 = (inst s t)
in (

let uu____568 = (

let uu____569 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____569))
in ((uu____567), (uu____568))))
in FStar_Syntax_Syntax.Tm_meta (uu____562))
in (mk uu____561))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____609 = (

let uu____610 = (

let uu____615 = (inst s t)
in (

let uu____616 = (

let uu____617 = (

let uu____622 = (inst s t')
in ((m), (uu____622)))
in FStar_Syntax_Syntax.Meta_monadic (uu____617))
in ((uu____615), (uu____616))))
in FStar_Syntax_Syntax.Tm_meta (uu____610))
in (mk uu____609))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(

let uu____629 = (

let uu____630 = (

let uu____635 = (inst s t)
in ((uu____635), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____630))
in (mk uu____629))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____649 -> (match (uu____649) with
| (x, imp) -> begin
(

let uu____656 = (

let uu___160_657 = x
in (

let uu____658 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___160_657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____658}))
in ((uu____656), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____684 -> (match (uu____684) with
| (a, imp) -> begin
(

let uu____691 = (inst s a)
in ((uu____691), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____710 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____710 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____719 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____719 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let uu___161_722 = ct
in (

let uu____723 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____726 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____732 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___157_736 -> (match (uu___157_736) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____740 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____740))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___161_722.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___161_722.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____723; FStar_Syntax_Syntax.effect_args = uu____726; FStar_Syntax_Syntax.flags = uu____732}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____785 = (

let uu____791 = (

let uu___162_792 = lc
in (

let uu____793 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___162_792.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____793; FStar_Syntax_Syntax.cflags = uu___162_792.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____796 -> (

let uu____797 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s uu____797)))}))
in FStar_Util.Inl (uu____791))
in Some (uu____785))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____816 -> begin
(

let inst_fv = (fun t fv -> (

let uu____824 = (FStar_Util.find_opt (fun uu____830 -> (match (uu____830) with
| (x, uu____834) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____824) with
| None -> begin
t
end
| Some (uu____841, us) -> begin
(mk t (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end)))
in (inst inst_fv t))
end))




