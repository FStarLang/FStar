
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _138_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _138_13 t.FStar_Syntax_Syntax.pos)))
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
(let _138_20 = (

let _38_52 = x
in (let _138_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_19}))
in ((_138_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _138_23 = (let _138_22 = (let _138_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_138_21)))
in FStar_Syntax_Syntax.Tm_abs (_138_22))
in (mk _138_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_62 -> (match (_38_62) with
| (x, imp) -> begin
(let _138_26 = (

let _38_63 = x
in (let _138_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_25}))
in ((_138_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _38_71 = bv
in (let _138_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _138_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _138_31 = (let _138_30 = (let _138_29 = (inst s t)
in (let _138_28 = (inst_args s args)
in ((_138_29), (_138_28))))
in FStar_Syntax_Syntax.Tm_app (_138_30))
in (mk _138_31))
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
(let _138_33 = (inst s w)
in Some (_138_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _138_36 = (let _138_35 = (let _138_34 = (inst s t)
in ((_138_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_138_35))
in (mk _138_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _138_41 = (let _138_40 = (let _138_39 = (inst s t1)
in (let _138_38 = (let _138_37 = (inst s t2)
in FStar_Util.Inl (_138_37))
in ((_138_39), (_138_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_138_40))
in (mk _138_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _138_46 = (let _138_45 = (let _138_44 = (inst s t1)
in (let _138_43 = (let _138_42 = (inst_comp s c)
in FStar_Util.Inr (_138_42))
in ((_138_44), (_138_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_138_45))
in (mk _138_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _138_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _38_110 = lb
in (let _138_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _138_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _38_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _38_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _138_49; FStar_Syntax_Syntax.lbeff = _38_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _138_48}))))))
in (((Prims.fst lbs)), (_138_50)))
in (let _138_53 = (let _138_52 = (let _138_51 = (inst s t)
in ((lbs), (_138_51)))
in FStar_Syntax_Syntax.Tm_let (_138_52))
in (mk _138_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _138_58 = (let _138_57 = (let _138_56 = (inst s t)
in (let _138_55 = (let _138_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_138_54))
in ((_138_56), (_138_55))))
in FStar_Syntax_Syntax.Tm_meta (_138_57))
in (mk _138_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _138_64 = (let _138_63 = (let _138_62 = (inst s t)
in (let _138_61 = (let _138_60 = (let _138_59 = (inst s t')
in ((m), (_138_59)))
in FStar_Syntax_Syntax.Meta_monadic (_138_60))
in ((_138_62), (_138_61))))
in FStar_Syntax_Syntax.Tm_meta (_138_63))
in (mk _138_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _138_67 = (let _138_66 = (let _138_65 = (inst s t)
in ((_138_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_138_66))
in (mk _138_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_133 -> (match (_38_133) with
| (a, imp) -> begin
(let _138_71 = (inst s a)
in ((_138_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _138_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _138_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _138_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _138_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _38_146 = ct
in (let _138_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _138_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _138_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _38_1 -> (match (_38_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _138_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_138_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _38_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _138_80; FStar_Syntax_Syntax.effect_args = _138_79; FStar_Syntax_Syntax.flags = _138_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _138_87 = (let _138_86 = (

let _38_163 = lc
in (let _138_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _38_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _138_85; FStar_Syntax_Syntax.cflags = _38_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _38_165 -> (match (()) with
| () -> begin
(let _138_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _138_84))
end))}))
in FStar_Util.Inl (_138_86))
in Some (_138_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _38_170 -> begin
(inst i t)
end))




