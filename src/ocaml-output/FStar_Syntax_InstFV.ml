
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _134_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _134_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _37_37 -> (match (_37_37) with
| (x, _37_36) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_37_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_51 -> (match (_37_51) with
| (x, imp) -> begin
(let _134_20 = (

let _37_52 = x
in (let _134_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _134_19}))
in ((_134_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _134_23 = (let _134_22 = (let _134_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_134_21)))
in FStar_Syntax_Syntax.Tm_abs (_134_22))
in (mk _134_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _134_26 = (

let _37_63 = x
in (let _134_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _134_25}))
in ((_134_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _37_71 = bv
in (let _134_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _134_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_31 = (let _134_30 = (let _134_29 = (inst s t)
in (let _134_28 = (inst_args s args)
in ((_134_29), (_134_28))))
in FStar_Syntax_Syntax.Tm_app (_134_30))
in (mk _134_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _37_86 -> (match (_37_86) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _134_33 = (inst s w)
in Some (_134_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _134_36 = (let _134_35 = (let _134_34 = (inst s t)
in ((_134_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_134_35))
in (mk _134_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _134_41 = (let _134_40 = (let _134_39 = (inst s t1)
in (let _134_38 = (let _134_37 = (inst s t2)
in FStar_Util.Inl (_134_37))
in ((_134_39), (_134_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_134_40))
in (mk _134_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _134_46 = (let _134_45 = (let _134_44 = (inst s t1)
in (let _134_43 = (let _134_42 = (inst_comp s c)
in FStar_Util.Inr (_134_42))
in ((_134_44), (_134_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_134_45))
in (mk _134_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _134_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _37_110 = lb
in (let _134_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _134_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _134_48}))))))
in (((Prims.fst lbs)), (_134_50)))
in (let _134_53 = (let _134_52 = (let _134_51 = (inst s t)
in ((lbs), (_134_51)))
in FStar_Syntax_Syntax.Tm_let (_134_52))
in (mk _134_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _134_58 = (let _134_57 = (let _134_56 = (inst s t)
in (let _134_55 = (let _134_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_134_54))
in ((_134_56), (_134_55))))
in FStar_Syntax_Syntax.Tm_meta (_134_57))
in (mk _134_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _134_64 = (let _134_63 = (let _134_62 = (inst s t)
in (let _134_61 = (let _134_60 = (let _134_59 = (inst s t')
in ((m), (_134_59)))
in FStar_Syntax_Syntax.Meta_monadic (_134_60))
in ((_134_62), (_134_61))))
in FStar_Syntax_Syntax.Tm_meta (_134_63))
in (mk _134_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _134_67 = (let _134_66 = (let _134_65 = (inst s t)
in ((_134_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_134_66))
in (mk _134_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_133 -> (match (_37_133) with
| (a, imp) -> begin
(let _134_71 = (inst s a)
in ((_134_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _134_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _134_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _134_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _134_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _37_146 = ct
in (let _134_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _134_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _134_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _134_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_134_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _37_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _37_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _134_80; FStar_Syntax_Syntax.effect_args = _134_79; FStar_Syntax_Syntax.flags = _134_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _134_87 = (let _134_86 = (

let _37_163 = lc
in (let _134_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _134_85; FStar_Syntax_Syntax.cflags = _37_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_165 -> (match (()) with
| () -> begin
(let _134_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _134_84))
end))}))
in FStar_Util.Inl (_134_86))
in Some (_134_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_170 -> begin
(inst i t)
end))




