
open Prims
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

let rec inst = (fun s t -> (let t = (FStar_Syntax_Subst.compress t)
in (let mk = (fun s -> (let _117_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _117_13 t.FStar_Syntax_Syntax.pos)))
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
(let _117_20 = (let _40_52 = x
in (let _117_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _117_19}))
in (_117_20, imp))
end))))
in (let body = (inst s body)
in (let _117_23 = (let _117_22 = (let _117_21 = (inst_lcomp_opt s lopt)
in (bs, body, _117_21))
in FStar_Syntax_Syntax.Tm_abs (_117_22))
in (mk _117_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _40_62 -> (match (_40_62) with
| (x, imp) -> begin
(let _117_26 = (let _40_63 = x
in (let _117_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _117_25}))
in (_117_26, imp))
end))))
in (let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let bv = (let _40_71 = bv
in (let _117_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _40_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _40_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _117_27}))
in (let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _117_31 = (let _117_30 = (let _117_29 = (inst s t)
in (let _117_28 = (inst_args s args)
in (_117_29, _117_28)))
in FStar_Syntax_Syntax.Tm_app (_117_30))
in (mk _117_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _40_86 -> (match (_40_86) with
| (p, wopt, t) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _117_33 = (inst s w)
in Some (_117_33))
end)
in (let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _117_36 = (let _117_35 = (let _117_34 = (inst s t)
in (_117_34, pats))
in FStar_Syntax_Syntax.Tm_match (_117_35))
in (mk _117_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, f) -> begin
(let _117_40 = (let _117_39 = (let _117_38 = (inst s t1)
in (let _117_37 = (inst s t2)
in (_117_38, _117_37, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_117_39))
in (mk _117_40))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let lbs = (let _117_44 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _40_103 = lb
in (let _117_43 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _117_42 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _40_103.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _40_103.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _117_43; FStar_Syntax_Syntax.lbeff = _40_103.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _117_42}))))))
in ((Prims.fst lbs), _117_44))
in (let _117_47 = (let _117_46 = (let _117_45 = (inst s t)
in (lbs, _117_45))
in FStar_Syntax_Syntax.Tm_let (_117_46))
in (mk _117_47)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _117_52 = (let _117_51 = (let _117_50 = (inst s t)
in (let _117_49 = (let _117_48 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_117_48))
in (_117_50, _117_49)))
in FStar_Syntax_Syntax.Tm_meta (_117_51))
in (mk _117_52))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _117_55 = (let _117_54 = (let _117_53 = (inst s t)
in (_117_53, tag))
in FStar_Syntax_Syntax.Tm_meta (_117_54))
in (mk _117_55))
end))))
and inst_args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _40_119 -> (match (_40_119) with
| (a, imp) -> begin
(let _117_59 = (inst s a)
in (_117_59, imp))
end)))))
and inst_comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _117_62 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _117_62))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _117_63 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _117_63))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let ct = (let _40_128 = ct
in (let _117_68 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _117_67 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _117_66 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _40_1 -> (match (_40_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _117_65 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_117_65))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _40_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _117_68; FStar_Syntax_Syntax.effect_args = _117_67; FStar_Syntax_Syntax.flags = _117_66}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _117_74 = (let _40_140 = lc
in (let _117_73 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _40_140.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _117_73; FStar_Syntax_Syntax.cflags = _40_140.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _40_142 -> (match (()) with
| () -> begin
(let _117_72 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _117_72))
end))}))
in Some (_117_74))
end))




