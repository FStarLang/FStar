
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _131_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _131_13 t.FStar_Syntax_Syntax.pos)))
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
(let _131_20 = (

let _37_52 = x
in (let _131_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _131_19}))
in ((_131_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _131_23 = (let _131_22 = (let _131_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_131_21)))
in FStar_Syntax_Syntax.Tm_abs (_131_22))
in (mk _131_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _131_26 = (

let _37_63 = x
in (let _131_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _131_25}))
in ((_131_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _37_71 = bv
in (let _131_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _131_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _131_31 = (let _131_30 = (let _131_29 = (inst s t)
in (let _131_28 = (inst_args s args)
in ((_131_29), (_131_28))))
in FStar_Syntax_Syntax.Tm_app (_131_30))
in (mk _131_31))
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
(let _131_33 = (inst s w)
in Some (_131_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _131_36 = (let _131_35 = (let _131_34 = (inst s t)
in ((_131_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_131_35))
in (mk _131_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _131_41 = (let _131_40 = (let _131_39 = (inst s t1)
in (let _131_38 = (let _131_37 = (inst s t2)
in FStar_Util.Inl (_131_37))
in ((_131_39), (_131_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_131_40))
in (mk _131_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _131_46 = (let _131_45 = (let _131_44 = (inst s t1)
in (let _131_43 = (let _131_42 = (inst_comp s c)
in FStar_Util.Inr (_131_42))
in ((_131_44), (_131_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_131_45))
in (mk _131_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _131_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _37_110 = lb
in (let _131_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _131_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _131_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _131_48}))))))
in (((Prims.fst lbs)), (_131_50)))
in (let _131_53 = (let _131_52 = (let _131_51 = (inst s t)
in ((lbs), (_131_51)))
in FStar_Syntax_Syntax.Tm_let (_131_52))
in (mk _131_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _131_58 = (let _131_57 = (let _131_56 = (inst s t)
in (let _131_55 = (let _131_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_131_54))
in ((_131_56), (_131_55))))
in FStar_Syntax_Syntax.Tm_meta (_131_57))
in (mk _131_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _131_64 = (let _131_63 = (let _131_62 = (inst s t)
in (let _131_61 = (let _131_60 = (let _131_59 = (inst s t')
in ((m), (_131_59)))
in FStar_Syntax_Syntax.Meta_monadic (_131_60))
in ((_131_62), (_131_61))))
in FStar_Syntax_Syntax.Tm_meta (_131_63))
in (mk _131_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _131_67 = (let _131_66 = (let _131_65 = (inst s t)
in ((_131_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_131_66))
in (mk _131_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_133 -> (match (_37_133) with
| (a, imp) -> begin
(let _131_71 = (inst s a)
in ((_131_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _131_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _131_74 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _131_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _131_75 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _37_146 = ct
in (let _131_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _131_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _131_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _131_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_131_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = _37_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _37_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _131_80; FStar_Syntax_Syntax.effect_args = _131_79; FStar_Syntax_Syntax.flags = _131_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _131_87 = (let _131_86 = (

let _37_163 = lc
in (let _131_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_163.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _131_85; FStar_Syntax_Syntax.cflags = _37_163.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_165 -> (match (()) with
| () -> begin
(let _131_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _131_84))
end))}))
in FStar_Util.Inl (_131_86))
in Some (_131_87))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_170 -> begin
(inst i t)
end))




