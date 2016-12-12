
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _132_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _132_13 t.FStar_Syntax_Syntax.pos)))
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
(let _132_20 = (

let _37_52 = x
in (let _132_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_19}))
in ((_132_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _132_23 = (let _132_22 = (let _132_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_132_21)))
in FStar_Syntax_Syntax.Tm_abs (_132_22))
in (mk _132_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _132_26 = (

let _37_63 = x
in (let _132_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_25}))
in ((_132_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _37_71 = bv
in (let _132_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _132_31 = (let _132_30 = (let _132_29 = (inst s t)
in (let _132_28 = (inst_args s args)
in ((_132_29), (_132_28))))
in FStar_Syntax_Syntax.Tm_app (_132_30))
in (mk _132_31))
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
(let _132_33 = (inst s w)
in Some (_132_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _132_36 = (let _132_35 = (let _132_34 = (inst s t)
in ((_132_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_132_35))
in (mk _132_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _132_41 = (let _132_40 = (let _132_39 = (inst s t1)
in (let _132_38 = (let _132_37 = (inst s t2)
in FStar_Util.Inl (_132_37))
in ((_132_39), (_132_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_132_40))
in (mk _132_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _132_46 = (let _132_45 = (let _132_44 = (inst s t1)
in (let _132_43 = (let _132_42 = (inst_comp s c)
in FStar_Util.Inr (_132_42))
in ((_132_44), (_132_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_132_45))
in (mk _132_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _132_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _37_110 = lb
in (let _132_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _132_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _132_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _132_48}))))))
in (((Prims.fst lbs)), (_132_50)))
in (let _132_53 = (let _132_52 = (let _132_51 = (inst s t)
in ((lbs), (_132_51)))
in FStar_Syntax_Syntax.Tm_let (_132_52))
in (mk _132_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _132_58 = (let _132_57 = (let _132_56 = (inst s t)
in (let _132_55 = (let _132_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_132_54))
in ((_132_56), (_132_55))))
in FStar_Syntax_Syntax.Tm_meta (_132_57))
in (mk _132_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _132_64 = (let _132_63 = (let _132_62 = (inst s t)
in (let _132_61 = (let _132_60 = (let _132_59 = (inst s t')
in ((m), (_132_59)))
in FStar_Syntax_Syntax.Meta_monadic (_132_60))
in ((_132_62), (_132_61))))
in FStar_Syntax_Syntax.Tm_meta (_132_63))
in (mk _132_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _132_67 = (let _132_66 = (let _132_65 = (inst s t)
in ((_132_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_132_66))
in (mk _132_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_133 -> (match (_37_133) with
| (a, imp) -> begin
(let _132_71 = (inst s a)
in ((_132_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _132_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _132_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _132_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _132_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _37_146 = ct
in (let _132_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _132_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _132_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _132_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_132_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _37_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _37_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _132_80; FStar_Syntax_Syntax.effect_args = _132_79; FStar_Syntax_Syntax.flags = _132_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _132_87 = (let _132_86 = (

let _37_163 = lc
in (let _132_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _132_85; FStar_Syntax_Syntax.cflags = _37_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_165 -> (match (()) with
| () -> begin
(let _132_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _132_84))
end))}))
in FStar_Util.Inl (_132_86))
in Some (_132_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_170 -> begin
(inst i t)
end))




