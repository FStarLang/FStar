
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (let _136_3 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _136_3 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (mk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_9) -> begin
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
in (let _136_48 = (let _136_47 = (let _136_46 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_136_46)))
in FStar_Syntax_Syntax.Tm_abs (_136_47))
in (mk _136_48))))
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

let _37_52 = bv
in (let _136_49 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_49}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _136_53 = (let _136_52 = (let _136_51 = (inst s t)
in (let _136_50 = (inst_args s args)
in ((_136_51), (_136_50))))
in FStar_Syntax_Syntax.Tm_app (_136_52))
in (mk _136_53))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _37_67 -> (match (_37_67) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _136_55 = (inst s w)
in Some (_136_55))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _136_58 = (let _136_57 = (let _136_56 = (inst s t)
in ((_136_56), (pats)))
in FStar_Syntax_Syntax.Tm_match (_136_57))
in (mk _136_58)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _136_63 = (let _136_62 = (let _136_61 = (inst s t1)
in (let _136_60 = (let _136_59 = (inst s t2)
in FStar_Util.Inl (_136_59))
in ((_136_61), (_136_60), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_136_62))
in (mk _136_63))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _136_68 = (let _136_67 = (let _136_66 = (inst s t1)
in (let _136_65 = (let _136_64 = (inst_comp s c)
in FStar_Util.Inr (_136_64))
in ((_136_66), (_136_65), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_136_67))
in (mk _136_68))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _136_72 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _37_91 = lb
in (let _136_71 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _136_70 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_91.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_91.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _136_71; FStar_Syntax_Syntax.lbeff = _37_91.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _136_70}))))))
in (((Prims.fst lbs)), (_136_72)))
in (let _136_75 = (let _136_74 = (let _136_73 = (inst s t)
in ((lbs), (_136_73)))
in FStar_Syntax_Syntax.Tm_let (_136_74))
in (mk _136_75)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _136_80 = (let _136_79 = (let _136_78 = (inst s t)
in (let _136_77 = (let _136_76 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_136_76))
in ((_136_78), (_136_77))))
in FStar_Syntax_Syntax.Tm_meta (_136_79))
in (mk _136_80))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _136_86 = (let _136_85 = (let _136_84 = (inst s t)
in (let _136_83 = (let _136_82 = (let _136_81 = (inst s t')
in ((m), (_136_81)))
in FStar_Syntax_Syntax.Meta_monadic (_136_82))
in ((_136_84), (_136_83))))
in FStar_Syntax_Syntax.Tm_meta (_136_85))
in (mk _136_86))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _136_89 = (let _136_88 = (let _136_87 = (inst s t)
in ((_136_87), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_136_88))
in (mk _136_89))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun _37_114 -> (match (_37_114) with
| (x, imp) -> begin
(let _136_100 = (

let _37_115 = x
in (let _136_99 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_99}))
in ((_136_100), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_121 -> (match (_37_121) with
| (a, imp) -> begin
(let _136_110 = (inst s a)
in ((_136_110), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _136_119 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _136_119 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _136_120 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _136_120 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _37_134 = ct
in (let _136_125 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _136_124 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _136_123 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _136_122 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_136_122))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _37_134.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _37_134.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _136_125; FStar_Syntax_Syntax.effect_args = _136_124; FStar_Syntax_Syntax.flags = _136_123}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _136_138 = (let _136_137 = (

let _37_151 = lc
in (let _136_136 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_151.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _136_136; FStar_Syntax_Syntax.cflags = _37_151.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_153 -> (match (()) with
| () -> begin
(let _136_135 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _136_135))
end))}))
in FStar_Util.Inl (_136_137))
in Some (_136_138))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_158 -> begin
(

let inst_fv = (fun t fv -> (match ((FStar_Util.find_opt (fun _37_165 -> (match (_37_165) with
| (x, _37_164) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)) with
| None -> begin
t
end
| Some (_37_168, us) -> begin
(mk t (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end))
in (inst inst_fv t))
end))




