
open Prims
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (let t = (FStar_Syntax_Subst.compress t)
in (let mk = (fun s -> (let _143_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _143_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_40_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _40_37 -> (match (_40_37) with
| (x, _40_36) -> begin
(FStar_Ident.lid_equals x (Prims.fst fv).FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_40_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _40_51 -> (match (_40_51) with
| (x, imp) -> begin
(let _143_20 = (let _40_52 = x
in (let _143_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_19}))
in (_143_20, imp))
end))))
in (let body = (inst s body)
in (let _143_23 = (let _143_22 = (let _143_21 = (inst_lcomp_opt s lopt)
in (bs, body, _143_21))
in FStar_Syntax_Syntax.Tm_abs (_143_22))
in (mk _143_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _40_62 -> (match (_40_62) with
| (x, imp) -> begin
(let _143_26 = (let _40_63 = x
in (let _143_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_25}))
in (_143_26, imp))
end))))
in (let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let bv = (let _40_71 = bv
in (let _143_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_27}))
in (let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _143_31 = (let _143_30 = (let _143_29 = (inst s t)
in (let _143_28 = (inst_args s args)
in (_143_29, _143_28)))
in FStar_Syntax_Syntax.Tm_app (_143_30))
in (mk _143_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _40_86 -> (match (_40_86) with
| (p, wopt, t) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _143_33 = (inst s w)
in Some (_143_33))
end)
in (let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _143_36 = (let _143_35 = (let _143_34 = (inst s t)
in (_143_34, pats))
in FStar_Syntax_Syntax.Tm_match (_143_35))
in (mk _143_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, f) -> begin
(let _143_40 = (let _143_39 = (let _143_38 = (inst s t1)
in (let _143_37 = (inst s t2)
in (_143_38, _143_37, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_143_39))
in (mk _143_40))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let lbs = (let _143_44 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _40_103 = lb
in (let _143_43 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _143_42 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _40_103.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _40_103.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _143_43; FStar_Syntax_Syntax.lbeff = _40_103.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _143_42}))))))
in ((Prims.fst lbs), _143_44))
in (let _143_47 = (let _143_46 = (let _143_45 = (inst s t)
in (lbs, _143_45))
in FStar_Syntax_Syntax.Tm_let (_143_46))
in (mk _143_47)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _143_52 = (let _143_51 = (let _143_50 = (inst s t)
in (let _143_49 = (let _143_48 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_143_48))
in (_143_50, _143_49)))
in FStar_Syntax_Syntax.Tm_meta (_143_51))
in (mk _143_52))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _143_55 = (let _143_54 = (let _143_53 = (inst s t)
in (_143_53, tag))
in FStar_Syntax_Syntax.Tm_meta (_143_54))
in (mk _143_55))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _40_119 -> (match (_40_119) with
| (a, imp) -> begin
(let _143_59 = (inst s a)
in (_143_59, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _143_62 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _143_62))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _143_63 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _143_63))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let ct = (let _40_128 = ct
in (let _143_68 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _143_67 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _143_66 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _40_1 -> (match (_40_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _143_65 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_143_65))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _40_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _143_68; FStar_Syntax_Syntax.effect_args = _143_67; FStar_Syntax_Syntax.flags = _143_66}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _143_74 = (let _40_140 = lc
in (let _143_73 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _40_140.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _143_73; FStar_Syntax_Syntax.cflags = _40_140.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _40_142 -> (match (()) with
| () -> begin
(let _143_72 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _143_72))
end))}))
in Some (_143_74))
end))




