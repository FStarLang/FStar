
open Prims
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

let rec inst = (fun s t -> (let t = (FStar_Syntax_Subst.compress t)
in (let mk = (fun s -> (let _91_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _91_13 t.FStar_Syntax_Syntax.pos)))
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
(FStar_Ident.lid_equals x (Prims.fst fv).FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_38_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_51 -> (match (_38_51) with
| (x, imp) -> begin
(let _91_20 = (let _38_52 = x
in (let _91_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _91_19}))
in (_91_20, imp))
end))))
in (let body = (inst s body)
in (let _91_23 = (let _91_22 = (let _91_21 = (inst_lcomp_opt s lopt)
in (bs, body, _91_21))
in FStar_Syntax_Syntax.Tm_abs (_91_22))
in (mk _91_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _38_62 -> (match (_38_62) with
| (x, imp) -> begin
(let _91_26 = (let _38_63 = x
in (let _91_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _91_25}))
in (_91_26, imp))
end))))
in (let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let bv = (let _38_71 = bv
in (let _91_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _38_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _38_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _91_27}))
in (let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _91_31 = (let _91_30 = (let _91_29 = (inst s t)
in (let _91_28 = (inst_args s args)
in (_91_29, _91_28)))
in FStar_Syntax_Syntax.Tm_app (_91_30))
in (mk _91_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _38_86 -> (match (_38_86) with
| (p, wopt, t) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _91_33 = (inst s w)
in Some (_91_33))
end)
in (let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _91_36 = (let _91_35 = (let _91_34 = (inst s t)
in (_91_34, pats))
in FStar_Syntax_Syntax.Tm_match (_91_35))
in (mk _91_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, f) -> begin
(let _91_40 = (let _91_39 = (let _91_38 = (inst s t1)
in (let _91_37 = (inst s t2)
in (_91_38, _91_37, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_91_39))
in (mk _91_40))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let lbs = (let _91_44 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _38_103 = lb
in (let _91_43 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _91_42 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _38_103.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _38_103.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _91_43; FStar_Syntax_Syntax.lbeff = _38_103.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _91_42}))))))
in ((Prims.fst lbs), _91_44))
in (let _91_47 = (let _91_46 = (let _91_45 = (inst s t)
in (lbs, _91_45))
in FStar_Syntax_Syntax.Tm_let (_91_46))
in (mk _91_47)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _91_52 = (let _91_51 = (let _91_50 = (inst s t)
in (let _91_49 = (let _91_48 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_91_48))
in (_91_50, _91_49)))
in FStar_Syntax_Syntax.Tm_meta (_91_51))
in (mk _91_52))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _91_55 = (let _91_54 = (let _91_53 = (inst s t)
in (_91_53, tag))
in FStar_Syntax_Syntax.Tm_meta (_91_54))
in (mk _91_55))
end))))
and inst_args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_119 -> (match (_38_119) with
| (a, imp) -> begin
(let _91_59 = (inst s a)
in (_91_59, imp))
end)))))
and inst_comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _91_62 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _91_62))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _91_63 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _91_63))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let ct = (let _38_128 = ct
in (let _91_68 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _91_67 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _91_66 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _38_1 -> (match (_38_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _91_65 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_91_65))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _38_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _91_68; FStar_Syntax_Syntax.effect_args = _91_67; FStar_Syntax_Syntax.flags = _91_66}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _91_74 = (let _38_140 = lc
in (let _91_73 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _38_140.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _91_73; FStar_Syntax_Syntax.cflags = _38_140.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _38_142 -> (match (()) with
| () -> begin
(let _91_72 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _91_72))
end))}))
in Some (_91_74))
end))




