
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _135_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _135_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_38_8) -> begin
(FStar_All.failwith "Impossible")
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
(let _135_20 = (

let _38_52 = x
in (let _135_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_19}))
in ((_135_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _135_23 = (let _135_22 = (let _135_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_135_21)))
in FStar_Syntax_Syntax.Tm_abs (_135_22))
in (mk _135_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_62 -> (match (_38_62) with
| (x, imp) -> begin
(let _135_26 = (

let _38_63 = x
in (let _135_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_25}))
in ((_135_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _38_71 = bv
in (let _135_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _135_31 = (let _135_30 = (let _135_29 = (inst s t)
in (let _135_28 = (inst_args s args)
in ((_135_29), (_135_28))))
in FStar_Syntax_Syntax.Tm_app (_135_30))
in (mk _135_31))
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
(let _135_33 = (inst s w)
in Some (_135_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _135_36 = (let _135_35 = (let _135_34 = (inst s t)
in ((_135_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_135_35))
in (mk _135_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _135_41 = (let _135_40 = (let _135_39 = (inst s t1)
in (let _135_38 = (let _135_37 = (inst s t2)
in FStar_Util.Inl (_135_37))
in ((_135_39), (_135_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_135_40))
in (mk _135_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _135_46 = (let _135_45 = (let _135_44 = (inst s t1)
in (let _135_43 = (let _135_42 = (inst_comp s c)
in FStar_Util.Inr (_135_42))
in ((_135_44), (_135_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_135_45))
in (mk _135_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _135_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _38_110 = lb
in (let _135_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _135_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _38_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _38_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _135_49; FStar_Syntax_Syntax.lbeff = _38_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _135_48}))))))
in (((Prims.fst lbs)), (_135_50)))
in (let _135_53 = (let _135_52 = (let _135_51 = (inst s t)
in ((lbs), (_135_51)))
in FStar_Syntax_Syntax.Tm_let (_135_52))
in (mk _135_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _135_58 = (let _135_57 = (let _135_56 = (inst s t)
in (let _135_55 = (let _135_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_135_54))
in ((_135_56), (_135_55))))
in FStar_Syntax_Syntax.Tm_meta (_135_57))
in (mk _135_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _135_64 = (let _135_63 = (let _135_62 = (inst s t)
in (let _135_61 = (let _135_60 = (let _135_59 = (inst s t')
in ((m), (_135_59)))
in FStar_Syntax_Syntax.Meta_monadic (_135_60))
in ((_135_62), (_135_61))))
in FStar_Syntax_Syntax.Tm_meta (_135_63))
in (mk _135_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _135_67 = (let _135_66 = (let _135_65 = (inst s t)
in ((_135_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_135_66))
in (mk _135_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_133 -> (match (_38_133) with
| (a, imp) -> begin
(let _135_71 = (inst s a)
in ((_135_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _135_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _135_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _135_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _135_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _38_146 = ct
in (let _135_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _135_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _135_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _38_1 -> (match (_38_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _135_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_135_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _38_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _135_80; FStar_Syntax_Syntax.effect_args = _135_79; FStar_Syntax_Syntax.flags = _135_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _135_87 = (let _135_86 = (

let _38_163 = lc
in (let _135_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _38_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _135_85; FStar_Syntax_Syntax.cflags = _38_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _38_165 -> (match (()) with
| () -> begin
(let _135_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _135_84))
end))}))
in FStar_Util.Inl (_135_86))
in Some (_135_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _38_170 -> begin
(inst i t)
end))




