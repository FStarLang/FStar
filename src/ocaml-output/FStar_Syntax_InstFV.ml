
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (fun s -> (let _129_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _129_13 t.FStar_Syntax_Syntax.pos)))
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
(let _129_20 = (

let _37_52 = x
in (let _129_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_19}))
in ((_129_20), (imp)))
end))))
in (

let body = (inst s body)
in (let _129_23 = (let _129_22 = (let _129_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_129_21)))
in FStar_Syntax_Syntax.Tm_abs (_129_22))
in (mk _129_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _129_26 = (

let _37_63 = x
in (let _129_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_25}))
in ((_129_26), (imp)))
end))))
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let _37_71 = bv
in (let _129_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_27}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _129_31 = (let _129_30 = (let _129_29 = (inst s t)
in (let _129_28 = (inst_args s args)
in ((_129_29), (_129_28))))
in FStar_Syntax_Syntax.Tm_app (_129_30))
in (mk _129_31))
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
(let _129_33 = (inst s w)
in Some (_129_33))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _129_36 = (let _129_35 = (let _129_34 = (inst s t)
in ((_129_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_129_35))
in (mk _129_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _129_41 = (let _129_40 = (let _129_39 = (inst s t1)
in (let _129_38 = (let _129_37 = (inst s t2)
in FStar_Util.Inl (_129_37))
in ((_129_39), (_129_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_129_40))
in (mk _129_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _129_46 = (let _129_45 = (let _129_44 = (inst s t1)
in (let _129_43 = (let _129_42 = (inst_comp s c)
in FStar_Util.Inr (_129_42))
in ((_129_44), (_129_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_129_45))
in (mk _129_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _129_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let _37_110 = lb
in (let _129_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _129_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _129_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _129_48}))))))
in (((Prims.fst lbs)), (_129_50)))
in (let _129_53 = (let _129_52 = (let _129_51 = (inst s t)
in ((lbs), (_129_51)))
in FStar_Syntax_Syntax.Tm_let (_129_52))
in (mk _129_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _129_58 = (let _129_57 = (let _129_56 = (inst s t)
in (let _129_55 = (let _129_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_129_54))
in ((_129_56), (_129_55))))
in FStar_Syntax_Syntax.Tm_meta (_129_57))
in (mk _129_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _129_61 = (let _129_60 = (let _129_59 = (inst s t)
in ((_129_59), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_129_60))
in (mk _129_61))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_126 -> (match (_37_126) with
| (a, imp) -> begin
(let _129_65 = (inst s a)
in ((_129_65), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _129_68 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _129_68))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _129_69 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _129_69))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let _37_135 = ct
in (let _129_74 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _129_73 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _129_72 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _129_71 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_129_71))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _37_135.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _129_74; FStar_Syntax_Syntax.effect_args = _129_73; FStar_Syntax_Syntax.flags = _129_72}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _129_81 = (let _129_80 = (

let _37_152 = lc
in (let _129_79 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_152.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _129_79; FStar_Syntax_Syntax.cflags = _37_152.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_154 -> (match (()) with
| () -> begin
(let _129_78 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _129_78))
end))}))
in FStar_Util.Inl (_129_80))
in Some (_129_81))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_159 -> begin
(inst i t)
end))




