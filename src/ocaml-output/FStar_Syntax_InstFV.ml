
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (let _137_3 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _137_3 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (mk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_38_9) -> begin
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
in (let _137_48 = (let _137_47 = (let _137_46 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_137_46)))
in FStar_Syntax_Syntax.Tm_abs (_137_47))
in (mk _137_48))))
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

let _38_52 = bv
in (let _137_49 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_49}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _137_53 = (let _137_52 = (let _137_51 = (inst s t)
in (let _137_50 = (inst_args s args)
in ((_137_51), (_137_50))))
in FStar_Syntax_Syntax.Tm_app (_137_52))
in (mk _137_53))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _38_67 -> (match (_38_67) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_55 = (inst s w)
in Some (_137_55))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _137_58 = (let _137_57 = (let _137_56 = (inst s t)
in ((_137_56), (pats)))
in FStar_Syntax_Syntax.Tm_match (_137_57))
in (mk _137_58)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _137_63 = (let _137_62 = (let _137_61 = (inst s t1)
in (let _137_60 = (let _137_59 = (inst s t2)
in FStar_Util.Inl (_137_59))
in ((_137_61), (_137_60), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_137_62))
in (mk _137_63))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _137_68 = (let _137_67 = (let _137_66 = (inst s t1)
in (let _137_65 = (let _137_64 = (inst_comp s c)
in FStar_Util.Inr (_137_64))
in ((_137_66), (_137_65), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_137_67))
in (mk _137_68))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _137_72 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _38_91 = lb
in (let _137_71 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _137_70 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _38_91.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _38_91.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _137_71; FStar_Syntax_Syntax.lbeff = _38_91.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _137_70}))))))
in (((Prims.fst lbs)), (_137_72)))
in (let _137_75 = (let _137_74 = (let _137_73 = (inst s t)
in ((lbs), (_137_73)))
in FStar_Syntax_Syntax.Tm_let (_137_74))
in (mk _137_75)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _137_80 = (let _137_79 = (let _137_78 = (inst s t)
in (let _137_77 = (let _137_76 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_137_76))
in ((_137_78), (_137_77))))
in FStar_Syntax_Syntax.Tm_meta (_137_79))
in (mk _137_80))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _137_86 = (let _137_85 = (let _137_84 = (inst s t)
in (let _137_83 = (let _137_82 = (let _137_81 = (inst s t')
in ((m), (_137_81)))
in FStar_Syntax_Syntax.Meta_monadic (_137_82))
in ((_137_84), (_137_83))))
in FStar_Syntax_Syntax.Tm_meta (_137_85))
in (mk _137_86))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _137_89 = (let _137_88 = (let _137_87 = (inst s t)
in ((_137_87), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_137_88))
in (mk _137_89))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _38_114 -> (match (_38_114) with
| (x, imp) -> begin
(let _137_100 = (

let _38_115 = x
in (let _137_99 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_99}))
in ((_137_100), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_121 -> (match (_38_121) with
| (a, imp) -> begin
(let _137_110 = (inst s a)
in ((_137_110), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _137_119 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _137_119 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _137_120 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _137_120 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _38_134 = ct
in (let _137_125 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _137_124 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _137_123 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _38_1 -> (match (_38_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _137_122 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_137_122))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _38_134.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_134.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _137_125; FStar_Syntax_Syntax.effect_args = _137_124; FStar_Syntax_Syntax.flags = _137_123}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _137_138 = (let _137_137 = (

let _38_151 = lc
in (let _137_136 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _38_151.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _137_136; FStar_Syntax_Syntax.cflags = _38_151.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _38_153 -> (match (()) with
| () -> begin
(let _137_135 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _137_135))
end))}))
in FStar_Util.Inl (_137_137))
in Some (_137_138))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _38_158 -> begin
(

let inst_fv = (fun t fv -> (match ((FStar_Util.find_opt (fun _38_165 -> (match (_38_165) with
| (x, _38_164) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)) with
| None -> begin
t
end
| Some (_38_168, us) -> begin
(mk t (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end))
in (inst inst_fv t))
end))




