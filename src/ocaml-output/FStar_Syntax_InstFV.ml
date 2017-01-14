
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (let _140_3 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _140_3 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (mk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_8) -> begin
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
in (let _140_48 = (let _140_47 = (let _140_46 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_140_46)))
in FStar_Syntax_Syntax.Tm_abs (_140_47))
in (mk _140_48))))
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

let _39_51 = bv
in (let _140_49 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _39_51.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _39_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _140_49}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _140_53 = (let _140_52 = (let _140_51 = (inst s t)
in (let _140_50 = (inst_args s args)
in ((_140_51), (_140_50))))
in FStar_Syntax_Syntax.Tm_app (_140_52))
in (mk _140_53))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _39_66 -> (match (_39_66) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _140_55 = (inst s w)
in Some (_140_55))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _140_58 = (let _140_57 = (let _140_56 = (inst s t)
in ((_140_56), (pats)))
in FStar_Syntax_Syntax.Tm_match (_140_57))
in (mk _140_58)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _140_63 = (let _140_62 = (let _140_61 = (inst s t1)
in (let _140_60 = (let _140_59 = (inst s t2)
in FStar_Util.Inl (_140_59))
in ((_140_61), (_140_60), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_140_62))
in (mk _140_63))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _140_68 = (let _140_67 = (let _140_66 = (inst s t1)
in (let _140_65 = (let _140_64 = (inst_comp s c)
in FStar_Util.Inr (_140_64))
in ((_140_66), (_140_65), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_140_67))
in (mk _140_68))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _140_72 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _39_90 = lb
in (let _140_71 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _140_70 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _39_90.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _39_90.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _140_71; FStar_Syntax_Syntax.lbeff = _39_90.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _140_70}))))))
in (((Prims.fst lbs)), (_140_72)))
in (let _140_75 = (let _140_74 = (let _140_73 = (inst s t)
in ((lbs), (_140_73)))
in FStar_Syntax_Syntax.Tm_let (_140_74))
in (mk _140_75)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _140_80 = (let _140_79 = (let _140_78 = (inst s t)
in (let _140_77 = (let _140_76 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_140_76))
in ((_140_78), (_140_77))))
in FStar_Syntax_Syntax.Tm_meta (_140_79))
in (mk _140_80))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _140_86 = (let _140_85 = (let _140_84 = (inst s t)
in (let _140_83 = (let _140_82 = (let _140_81 = (inst s t')
in ((m), (_140_81)))
in FStar_Syntax_Syntax.Meta_monadic (_140_82))
in ((_140_84), (_140_83))))
in FStar_Syntax_Syntax.Tm_meta (_140_85))
in (mk _140_86))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _140_89 = (let _140_88 = (let _140_87 = (inst s t)
in ((_140_87), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_140_88))
in (mk _140_89))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _39_113 -> (match (_39_113) with
| (x, imp) -> begin
(let _140_100 = (

let _39_114 = x
in (let _140_99 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _39_114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _39_114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _140_99}))
in ((_140_100), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _39_120 -> (match (_39_120) with
| (a, imp) -> begin
(let _140_110 = (inst s a)
in ((_140_110), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _140_119 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _140_119 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _140_120 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _140_120 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _39_133 = ct
in (let _140_125 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _140_124 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _140_123 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___74 -> (match (uu___74) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _140_122 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_140_122))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _39_133.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _39_133.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _140_125; FStar_Syntax_Syntax.effect_args = _140_124; FStar_Syntax_Syntax.flags = _140_123}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _140_138 = (let _140_137 = (

let _39_150 = lc
in (let _140_136 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _39_150.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _140_136; FStar_Syntax_Syntax.cflags = _39_150.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _39_152 -> (match (()) with
| () -> begin
(let _140_135 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _140_135))
end))}))
in FStar_Util.Inl (_140_137))
in Some (_140_138))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _39_157 -> begin
(

let inst_fv = (fun t fv -> (match ((FStar_Util.find_opt (fun _39_164 -> (match (_39_164) with
| (x, _39_163) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)) with
| None -> begin
t
end
| Some (_39_167, us) -> begin
(mk t (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end))
in (inst inst_fv t))
end))




