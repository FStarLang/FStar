
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
| FStar_Syntax_Syntax.Tm_delayed (uu____146) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____170) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____171) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____184) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____197) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_bvar (uu____198) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____199) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_quoted (uu____200) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____207) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____214) -> begin
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

let uu____265 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____265)))
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

let uu___98_323 = bv
in (

let uu____324 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___98_323.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___98_323.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____324}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____356 = (

let uu____357 = (

let uu____374 = (inst s t2)
in (

let uu____377 = (inst_args s args)
in ((uu____374), (uu____377))))
in FStar_Syntax_Syntax.Tm_app (uu____357))
in (mk1 uu____356))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____509 -> (match (uu____509) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____547 = (inst s w)
in FStar_Pervasives_Native.Some (uu____547))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____553 = (

let uu____554 = (

let uu____577 = (inst s t2)
in ((uu____577), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____554))
in (mk1 uu____553)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____670 -> (match (uu____670) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____732 = (inst s t2)
in FStar_Util.Inl (uu____732))
end
| FStar_Util.Inr (c) -> begin
(

let uu____740 = (inst_comp s c)
in FStar_Util.Inr (uu____740))
end)
in ((annot1), (topt1))))
end))
in (

let uu____753 = (

let uu____754 = (

let uu____781 = (inst s t11)
in (

let uu____784 = (inst_asc asc)
in ((uu____781), (uu____784), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____754))
in (mk1 uu____753)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____849 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___99_864 = lb
in (

let uu____865 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____868 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___99_864.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___99_864.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____865; FStar_Syntax_Syntax.lbeff = uu___99_864.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____868; FStar_Syntax_Syntax.lbattrs = uu___99_864.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___99_864.FStar_Syntax_Syntax.lbpos}))))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____849)))
in (

let uu____877 = (

let uu____878 = (

let uu____892 = (inst s t2)
in ((lbs1), (uu____892)))
in FStar_Syntax_Syntax.Tm_let (uu____878))
in (mk1 uu____877)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____922 = (

let uu____923 = (

let uu____930 = (inst s t2)
in (

let uu____933 = (

let uu____934 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____934))
in ((uu____930), (uu____933))))
in FStar_Syntax_Syntax.Tm_meta (uu____923))
in (mk1 uu____922))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1004 = (

let uu____1005 = (

let uu____1012 = (inst s t2)
in (

let uu____1015 = (

let uu____1016 = (

let uu____1023 = (inst s t')
in ((m), (uu____1023)))
in FStar_Syntax_Syntax.Meta_monadic (uu____1016))
in ((uu____1012), (uu____1015))))
in FStar_Syntax_Syntax.Tm_meta (uu____1005))
in (mk1 uu____1004))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____1036 = (

let uu____1037 = (

let uu____1044 = (inst s t2)
in ((uu____1044), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____1037))
in (mk1 uu____1036))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____1079 -> (match (uu____1079) with
| (x, imp) -> begin
(

let uu____1098 = (

let uu___100_1099 = x
in (

let uu____1100 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___100_1099.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_1099.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1100}))
in ((uu____1098), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____1155 -> (match (uu____1155) with
| (a, imp) -> begin
(

let uu____1174 = (inst s a)
in ((uu____1174), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1197 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____1197 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1208 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1208 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___101_1211 = ct
in (

let uu____1212 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____1215 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____1226 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___97_1236 -> (match (uu___97_1236) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____1240 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____1240))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___101_1211.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___101_1211.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____1212; FStar_Syntax_Syntax.effect_args = uu____1215; FStar_Syntax_Syntax.flags = uu____1226}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____1255 = (

let uu___102_1256 = rc
in (

let uu____1257 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s))
in {FStar_Syntax_Syntax.residual_effect = uu___102_1256.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____1257; FStar_Syntax_Syntax.residual_flags = uu___102_1256.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____1255))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____1281 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____1293 = (FStar_Util.find_opt (fun uu____1307 -> (match (uu____1307) with
| (x, uu____1314) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____1293) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (uu____1319, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




