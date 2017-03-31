
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (

let uu____26 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s uu____26 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let mk1 = (mk t1)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____123) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(s t1 fv)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs1 = (inst_binders s bs)
in (

let body1 = (inst s body)
in (

let uu____179 = (

let uu____180 = (

let uu____195 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____195)))
in FStar_Syntax_Syntax.Tm_abs (uu____180))
in (mk1 uu____179))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (inst_binders s bs)
in (

let c1 = (inst_comp s c)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t2) -> begin
(

let bv1 = (

let uu___156_233 = bv
in (

let uu____234 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___156_233.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___156_233.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____234}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____254 = (

let uu____255 = (

let uu____265 = (inst s t2)
in (

let uu____266 = (inst_args s args)
in ((uu____265), (uu____266))))
in FStar_Syntax_Syntax.Tm_app (uu____255))
in (mk1 uu____254))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____343 -> (match (uu____343) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(

let uu____369 = (inst s w)
in Some (uu____369))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____374 = (

let uu____375 = (

let uu____391 = (inst s t2)
in ((uu____391), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____375))
in (mk1 uu____374)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____447 -> (match (uu____447) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____488 = (inst s t2)
in FStar_Util.Inl (uu____488))
end
| FStar_Util.Inr (c) -> begin
(

let uu____496 = (inst_comp s c)
in FStar_Util.Inr (uu____496))
end)
in ((annot1), (topt1))))
end))
in (

let uu____506 = (

let uu____507 = (

let uu____525 = (inst s t11)
in (

let uu____526 = (inst_asc asc)
in ((uu____525), (uu____526), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____507))
in (mk1 uu____506)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____558 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu___157_564 = lb
in (

let uu____565 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____568 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___157_564.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___157_564.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____565; FStar_Syntax_Syntax.lbeff = uu___157_564.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____568}))))))
in (((Prims.fst lbs)), (uu____558)))
in (

let uu____573 = (

let uu____574 = (

let uu____582 = (inst s t2)
in ((lbs1), (uu____582)))
in FStar_Syntax_Syntax.Tm_let (uu____574))
in (mk1 uu____573)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____598 = (

let uu____599 = (

let uu____604 = (inst s t2)
in (

let uu____605 = (

let uu____606 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____606))
in ((uu____604), (uu____605))))
in FStar_Syntax_Syntax.Tm_meta (uu____599))
in (mk1 uu____598))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____646 = (

let uu____647 = (

let uu____652 = (inst s t2)
in (

let uu____653 = (

let uu____654 = (

let uu____659 = (inst s t')
in ((m), (uu____659)))
in FStar_Syntax_Syntax.Meta_monadic (uu____654))
in ((uu____652), (uu____653))))
in FStar_Syntax_Syntax.Tm_meta (uu____647))
in (mk1 uu____646))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____666 = (

let uu____667 = (

let uu____672 = (inst s t2)
in ((uu____672), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____667))
in (mk1 uu____666))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____686 -> (match (uu____686) with
| (x, imp) -> begin
(

let uu____693 = (

let uu___158_694 = x
in (

let uu____695 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___158_694.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_694.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____695}))
in ((uu____693), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____721 -> (match (uu____721) with
| (a, imp) -> begin
(

let uu____728 = (inst s a)
in ((uu____728), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____747 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____747 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____756 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____756 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___159_759 = ct
in (

let uu____760 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____763 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____769 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___155_773 -> (match (uu___155_773) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____777 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____777))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___159_759.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___159_759.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____760; FStar_Syntax_Syntax.effect_args = uu____763; FStar_Syntax_Syntax.flags = uu____769}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____822 = (

let uu____828 = (

let uu___160_829 = lc
in (

let uu____830 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___160_829.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu____830; FStar_Syntax_Syntax.cflags = uu___160_829.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____833 -> (

let uu____834 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s uu____834)))}))
in FStar_Util.Inl (uu____828))
in Some (uu____822))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____853 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____861 = (FStar_Util.find_opt (fun uu____867 -> (match (uu____867) with
| (x, uu____871) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____861) with
| None -> begin
t1
end
| Some (uu____878, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




