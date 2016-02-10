
open Prims
# 23 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\instfv.fs"

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

# 24 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\instfv.fs"

let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (let t = (FStar_Syntax_Subst.compress t)
in (let mk = (fun s -> (let _141_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _141_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _39_37 -> (match (_39_37) with
| (x, _39_36) -> begin
(FStar_Ident.lid_equals x (Prims.fst fv).FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_39_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _39_51 -> (match (_39_51) with
| (x, imp) -> begin
(let _141_20 = (let _39_52 = x
in (let _141_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _39_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _39_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _141_19}))
in (_141_20, imp))
end))))
in (let body = (inst s body)
in (let _141_23 = (let _141_22 = (let _141_21 = (inst_lcomp_opt s lopt)
in (bs, body, _141_21))
in FStar_Syntax_Syntax.Tm_abs (_141_22))
in (mk _141_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _39_62 -> (match (_39_62) with
| (x, imp) -> begin
(let _141_26 = (let _39_63 = x
in (let _141_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _39_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _39_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _141_25}))
in (_141_26, imp))
end))))
in (let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let bv = (let _39_71 = bv
in (let _141_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _39_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _39_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _141_27}))
in (let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _141_31 = (let _141_30 = (let _141_29 = (inst s t)
in (let _141_28 = (inst_args s args)
in (_141_29, _141_28)))
in FStar_Syntax_Syntax.Tm_app (_141_30))
in (mk _141_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _39_86 -> (match (_39_86) with
| (p, wopt, t) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _141_33 = (inst s w)
in Some (_141_33))
end)
in (let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _141_36 = (let _141_35 = (let _141_34 = (inst s t)
in (_141_34, pats))
in FStar_Syntax_Syntax.Tm_match (_141_35))
in (mk _141_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, f) -> begin
(let _141_40 = (let _141_39 = (let _141_38 = (inst s t1)
in (let _141_37 = (inst s t2)
in (_141_38, _141_37, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_141_39))
in (mk _141_40))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let lbs = (let _141_44 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _39_103 = lb
in (let _141_43 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _141_42 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _39_103.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _39_103.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _141_43; FStar_Syntax_Syntax.lbeff = _39_103.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _141_42}))))))
in ((Prims.fst lbs), _141_44))
in (let _141_47 = (let _141_46 = (let _141_45 = (inst s t)
in (lbs, _141_45))
in FStar_Syntax_Syntax.Tm_let (_141_46))
in (mk _141_47)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _141_52 = (let _141_51 = (let _141_50 = (inst s t)
in (let _141_49 = (let _141_48 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_141_48))
in (_141_50, _141_49)))
in FStar_Syntax_Syntax.Tm_meta (_141_51))
in (mk _141_52))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _141_55 = (let _141_54 = (let _141_53 = (inst s t)
in (_141_53, tag))
in FStar_Syntax_Syntax.Tm_meta (_141_54))
in (mk _141_55))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _39_119 -> (match (_39_119) with
| (a, imp) -> begin
(let _141_59 = (inst s a)
in (_141_59, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _141_62 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _141_62))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _141_63 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _141_63))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let ct = (let _39_128 = ct
in (let _141_68 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _141_67 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _141_66 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _39_1 -> (match (_39_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _141_65 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_141_65))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _39_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _141_68; FStar_Syntax_Syntax.effect_args = _141_67; FStar_Syntax_Syntax.flags = _141_66}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _141_74 = (let _39_140 = lc
in (let _141_73 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _39_140.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _141_73; FStar_Syntax_Syntax.cflags = _39_140.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _39_142 -> (match (()) with
| () -> begin
(let _141_72 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _141_72))
end))}))
in Some (_141_74))
end))




