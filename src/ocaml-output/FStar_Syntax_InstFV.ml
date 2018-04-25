
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
| FStar_Syntax_Syntax.Tm_uvar (uu____184) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____201) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_bvar (uu____202) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____203) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_quoted (uu____204) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____211) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____218) -> begin
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

let uu____245 = (

let uu____246 = (

let uu____263 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____263)))
in FStar_Syntax_Syntax.Tm_abs (uu____246))
in (mk1 uu____245))))
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

let uu___30_299 = bv
in (

let uu____300 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___30_299.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___30_299.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____300}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____326 = (

let uu____327 = (

let uu____342 = (inst s t2)
in (

let uu____343 = (inst_args s args)
in ((uu____342), (uu____343))))
in FStar_Syntax_Syntax.Tm_app (uu____327))
in (mk1 uu____326))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____465 -> (match (uu____465) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____503 = (inst s w)
in FStar_Pervasives_Native.Some (uu____503))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____509 = (

let uu____510 = (

let uu____533 = (inst s t2)
in ((uu____533), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____510))
in (mk1 uu____509)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____618 -> (match (uu____618) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____680 = (inst s t2)
in FStar_Util.Inl (uu____680))
end
| FStar_Util.Inr (c) -> begin
(

let uu____688 = (inst_comp s c)
in FStar_Util.Inr (uu____688))
end)
in ((annot1), (topt1))))
end))
in (

let uu____701 = (

let uu____702 = (

let uu____729 = (inst s t11)
in (

let uu____730 = (inst_asc asc)
in ((uu____729), (uu____730), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____702))
in (mk1 uu____701)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____782 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___31_796 = lb
in (

let uu____797 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____800 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___31_796.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___31_796.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____797; FStar_Syntax_Syntax.lbeff = uu___31_796.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____800; FStar_Syntax_Syntax.lbattrs = uu___31_796.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___31_796.FStar_Syntax_Syntax.lbpos}))))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____782)))
in (

let uu____807 = (

let uu____808 = (

let uu____821 = (inst s t2)
in ((lbs1), (uu____821)))
in FStar_Syntax_Syntax.Tm_let (uu____808))
in (mk1 uu____807)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____844 = (

let uu____845 = (

let uu____852 = (inst s t2)
in (

let uu____853 = (

let uu____854 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____854))
in ((uu____852), (uu____853))))
in FStar_Syntax_Syntax.Tm_meta (uu____845))
in (mk1 uu____844))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____912 = (

let uu____913 = (

let uu____920 = (inst s t2)
in (

let uu____921 = (

let uu____922 = (

let uu____929 = (inst s t')
in ((m), (uu____929)))
in FStar_Syntax_Syntax.Meta_monadic (uu____922))
in ((uu____920), (uu____921))))
in FStar_Syntax_Syntax.Tm_meta (uu____913))
in (mk1 uu____912))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____936 = (

let uu____937 = (

let uu____944 = (inst s t2)
in ((uu____944), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____937))
in (mk1 uu____936))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____969 -> (match (uu____969) with
| (x, imp) -> begin
(

let uu____980 = (

let uu___32_981 = x
in (

let uu____982 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___32_981.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___32_981.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____982}))
in ((uu____980), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____1025 -> (match (uu____1025) with
| (a, imp) -> begin
(

let uu____1036 = (inst s a)
in ((uu____1036), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1057 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____1057 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1068 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1068 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___33_1071 = ct
in (

let uu____1072 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____1075 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____1084 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___29_1094 -> (match (uu___29_1094) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____1098 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____1098))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___33_1071.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___33_1071.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____1072; FStar_Syntax_Syntax.effect_args = uu____1075; FStar_Syntax_Syntax.flags = uu____1084}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____1113 = (

let uu___34_1114 = rc
in (

let uu____1115 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s))
in {FStar_Syntax_Syntax.residual_effect = uu___34_1114.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____1115; FStar_Syntax_Syntax.residual_flags = uu___34_1114.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____1113))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____1136 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____1148 = (FStar_Util.find_opt (fun uu____1162 -> (match (uu____1162) with
| (x, uu____1168) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____1148) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (uu____1173, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




