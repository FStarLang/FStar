
open Prims
open FStar_Pervasives

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (

let uu____31 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s uu____31 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let mk1 = (mk t1)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____118) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____133) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____134) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____145) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____156) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_bvar (uu____157) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____158) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____159) -> begin
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

let uu____182 = (

let uu____183 = (

let uu____193 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____193)))
in FStar_Syntax_Syntax.Tm_abs (uu____183))
in (mk1 uu____182))))
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

let uu___148_221 = bv
in (

let uu____222 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___148_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___148_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____222}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____242 = (

let uu____243 = (

let uu____253 = (inst s t2)
in (

let uu____254 = (inst_args s args)
in ((uu____253), (uu____254))))
in FStar_Syntax_Syntax.Tm_app (uu____243))
in (mk1 uu____242))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____330 -> (match (uu____330) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____352 = (inst s w)
in FStar_Pervasives_Native.Some (uu____352))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____356 = (

let uu____357 = (

let uu____372 = (inst s t2)
in ((uu____372), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____357))
in (mk1 uu____356)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____427 -> (match (uu____427) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____468 = (inst s t2)
in FStar_Util.Inl (uu____468))
end
| FStar_Util.Inr (c) -> begin
(

let uu____476 = (inst_comp s c)
in FStar_Util.Inr (uu____476))
end)
in ((annot1), (topt1))))
end))
in (

let uu____486 = (

let uu____487 = (

let uu____505 = (inst s t11)
in (

let uu____506 = (inst_asc asc)
in ((uu____505), (uu____506), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____487))
in (mk1 uu____486)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____538 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___149_548 = lb
in (

let uu____549 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____552 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___149_548.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___149_548.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____549; FStar_Syntax_Syntax.lbeff = uu___149_548.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____552}))))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____538)))
in (

let uu____557 = (

let uu____558 = (

let uu____566 = (inst s t2)
in ((lbs1), (uu____566)))
in FStar_Syntax_Syntax.Tm_let (uu____558))
in (mk1 uu____557)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____582 = (

let uu____583 = (

let uu____588 = (inst s t2)
in (

let uu____589 = (

let uu____590 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____590))
in ((uu____588), (uu____589))))
in FStar_Syntax_Syntax.Tm_meta (uu____583))
in (mk1 uu____582))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____630 = (

let uu____631 = (

let uu____636 = (inst s t2)
in (

let uu____637 = (

let uu____638 = (

let uu____643 = (inst s t')
in ((m), (uu____643)))
in FStar_Syntax_Syntax.Meta_monadic (uu____638))
in ((uu____636), (uu____637))))
in FStar_Syntax_Syntax.Tm_meta (uu____631))
in (mk1 uu____630))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____650 = (

let uu____651 = (

let uu____656 = (inst s t2)
in ((uu____656), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____651))
in (mk1 uu____650))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____674 -> (match (uu____674) with
| (x, imp) -> begin
(

let uu____681 = (

let uu___150_682 = x
in (

let uu____683 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___150_682.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___150_682.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____683}))
in ((uu____681), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____713 -> (match (uu____713) with
| (a, imp) -> begin
(

let uu____720 = (inst s a)
in ((uu____720), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____739 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____739 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____748 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____748 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___151_751 = ct
in (

let uu____752 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____755 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____761 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___147_768 -> (match (uu___147_768) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____772 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____772))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___151_751.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___151_751.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____752; FStar_Syntax_Syntax.effect_args = uu____755; FStar_Syntax_Syntax.flags = uu____761}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____785 = (

let uu___152_786 = rc
in (

let uu____787 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s))
in {FStar_Syntax_Syntax.residual_effect = uu___152_786.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____787; FStar_Syntax_Syntax.residual_flags = uu___152_786.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____785))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____803 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____811 = (FStar_Util.find_opt (fun uu____820 -> (match (uu____820) with
| (x, uu____824) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____811) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (uu____827, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




