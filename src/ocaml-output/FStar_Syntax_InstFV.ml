
open Prims
open FStar_Pervasives

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk : 'Auu____15 'Auu____16 . 'Auu____15 FStar_Syntax_Syntax.syntax  ->  'Auu____16  ->  'Auu____16 FStar_Syntax_Syntax.syntax = (fun t s -> (FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let mk1 = (mk t1)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____141) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____166) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____167) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____168) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____169) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_bvar (uu____170) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____171) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_quoted (uu____172) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____179) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____186) -> begin
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

let uu____213 = (

let uu____214 = (

let uu____231 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____231)))
in FStar_Syntax_Syntax.Tm_abs (uu____214))
in (mk1 uu____213))))
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

let uu___27_281 = bv
in (

let uu____282 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___27_281.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___27_281.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____282}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____310 = (

let uu____311 = (

let uu____326 = (inst s t2)
in (

let uu____329 = (inst_args s args)
in ((uu____326), (uu____329))))
in FStar_Syntax_Syntax.Tm_app (uu____311))
in (mk1 uu____310))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____453 -> (match (uu____453) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____491 = (inst s w)
in FStar_Pervasives_Native.Some (uu____491))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____497 = (

let uu____498 = (

let uu____521 = (inst s t2)
in ((uu____521), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____498))
in (mk1 uu____497)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____614 -> (match (uu____614) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____676 = (inst s t2)
in FStar_Util.Inl (uu____676))
end
| FStar_Util.Inr (c) -> begin
(

let uu____684 = (inst_comp s c)
in FStar_Util.Inr (uu____684))
end)
in ((annot1), (topt1))))
end))
in (

let uu____697 = (

let uu____698 = (

let uu____725 = (inst s t11)
in (

let uu____728 = (inst_asc asc)
in ((uu____725), (uu____728), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____698))
in (mk1 uu____697)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____790 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___28_804 = lb
in (

let uu____805 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____808 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___28_804.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___28_804.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____805; FStar_Syntax_Syntax.lbeff = uu___28_804.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____808; FStar_Syntax_Syntax.lbattrs = uu___28_804.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___28_804.FStar_Syntax_Syntax.lbpos}))))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____790)))
in (

let uu____815 = (

let uu____816 = (

let uu____829 = (inst s t2)
in ((lbs1), (uu____829)))
in FStar_Syntax_Syntax.Tm_let (uu____816))
in (mk1 uu____815)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____856 = (

let uu____857 = (

let uu____864 = (inst s t2)
in (

let uu____867 = (

let uu____868 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____868))
in ((uu____864), (uu____867))))
in FStar_Syntax_Syntax.Tm_meta (uu____857))
in (mk1 uu____856))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____928 = (

let uu____929 = (

let uu____936 = (inst s t2)
in (

let uu____939 = (

let uu____940 = (

let uu____947 = (inst s t')
in ((m), (uu____947)))
in FStar_Syntax_Syntax.Meta_monadic (uu____940))
in ((uu____936), (uu____939))))
in FStar_Syntax_Syntax.Tm_meta (uu____929))
in (mk1 uu____928))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____960 = (

let uu____961 = (

let uu____968 = (inst s t2)
in ((uu____968), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____961))
in (mk1 uu____960))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____997 -> (match (uu____997) with
| (x, imp) -> begin
(

let uu____1008 = (

let uu___29_1009 = x
in (

let uu____1010 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___29_1009.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___29_1009.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1010}))
in ((uu____1008), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____1053 -> (match (uu____1053) with
| (a, imp) -> begin
(

let uu____1064 = (inst s a)
in ((uu____1064), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1085 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____1085 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1096 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1096 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___30_1099 = ct
in (

let uu____1100 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____1103 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____1112 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___26_1122 -> (match (uu___26_1122) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____1126 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____1126))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___30_1099.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___30_1099.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____1100; FStar_Syntax_Syntax.effect_args = uu____1103; FStar_Syntax_Syntax.flags = uu____1112}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____1141 = (

let uu___31_1142 = rc
in (

let uu____1143 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s))
in {FStar_Syntax_Syntax.residual_effect = uu___31_1142.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____1143; FStar_Syntax_Syntax.residual_flags = uu___31_1142.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____1141))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____1166 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____1178 = (FStar_Util.find_opt (fun uu____1192 -> (match (uu____1192) with
| (x, uu____1198) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____1178) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (uu____1203, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




