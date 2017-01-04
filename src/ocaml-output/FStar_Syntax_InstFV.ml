
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _136_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _136_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_38_8) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _38_37 -> (match (_38_37) with
| (x, _38_36) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_38_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_51 -> (match (_38_51) with
| (x, imp) -> begin
(let _136_20 = (

let _38_52 = x
in (let _136_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_19}))
in ((_136_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _136_23 = (let _136_22 = (let _136_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_136_21)))
in FStar_Syntax_Syntax.Tm_abs (_136_22))
in (mk _136_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_62 -> (match (_38_62) with
| (x, imp) -> begin
(let _136_26 = (

let _38_63 = x
in (let _136_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_25}))
in ((_136_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _38_71 = bv
in (let _136_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _136_31 = (let _136_30 = (let _136_29 = (inst s t)
in (let _136_28 = (inst_args s args)
in ((_136_29), (_136_28))))
in FStar_Syntax_Syntax.Tm_app (_136_30))
in (mk _136_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _38_86 -> (match (_38_86) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _136_33 = (inst s w)
in Some (_136_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _136_36 = (let _136_35 = (let _136_34 = (inst s t)
in ((_136_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_136_35))
in (mk _136_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _136_41 = (let _136_40 = (let _136_39 = (inst s t1)
in (let _136_38 = (let _136_37 = (inst s t2)
in FStar_Util.Inl (_136_37))
in ((_136_39), (_136_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_136_40))
in (mk _136_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _136_46 = (let _136_45 = (let _136_44 = (inst s t1)
in (let _136_43 = (let _136_42 = (inst_comp s c)
in FStar_Util.Inr (_136_42))
in ((_136_44), (_136_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_136_45))
in (mk _136_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _136_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _38_110 = lb
in (let _136_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _136_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _38_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _38_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _136_49; FStar_Syntax_Syntax.lbeff = _38_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _136_48}))))))
in (((Prims.fst lbs)), (_136_50)))
in (let _136_53 = (let _136_52 = (let _136_51 = (inst s t)
in ((lbs), (_136_51)))
in FStar_Syntax_Syntax.Tm_let (_136_52))
in (mk _136_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _136_58 = (let _136_57 = (let _136_56 = (inst s t)
in (let _136_55 = (let _136_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_136_54))
in ((_136_56), (_136_55))))
in FStar_Syntax_Syntax.Tm_meta (_136_57))
in (mk _136_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _136_64 = (let _136_63 = (let _136_62 = (inst s t)
in (let _136_61 = (let _136_60 = (let _136_59 = (inst s t')
in ((m), (_136_59)))
in FStar_Syntax_Syntax.Meta_monadic (_136_60))
in ((_136_62), (_136_61))))
in FStar_Syntax_Syntax.Tm_meta (_136_63))
in (mk _136_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _136_67 = (let _136_66 = (let _136_65 = (inst s t)
in ((_136_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_136_66))
in (mk _136_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_133 -> (match (_38_133) with
| (a, imp) -> begin
(let _136_71 = (inst s a)
in ((_136_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _136_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _136_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _136_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _136_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _38_146 = ct
in (let _136_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _136_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _136_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _38_1 -> (match (_38_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _136_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_136_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _38_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _136_80; FStar_Syntax_Syntax.effect_args = _136_79; FStar_Syntax_Syntax.flags = _136_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _136_87 = (let _136_86 = (

let _38_163 = lc
in (let _136_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _38_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _136_85; FStar_Syntax_Syntax.cflags = _38_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _38_165 -> (match (()) with
| () -> begin
(let _136_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _136_84))
end))}))
in FStar_Util.Inl (_136_86))
in Some (_136_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _38_170 -> begin
(inst i t)
end))




