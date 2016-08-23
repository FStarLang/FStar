
open Prims
# 24 "FStar.Syntax.InstFV.fst"
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

# 27 "FStar.Syntax.InstFV.fst"
let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (
# 30 "FStar.Syntax.InstFV.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 31 "FStar.Syntax.InstFV.fst"
let mk = (fun s -> (let _130_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _130_13 t.FStar_Syntax_Syntax.pos)))
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
# 51 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_51 -> (match (_37_51) with
| (x, imp) -> begin
(let _130_20 = (
# 51 "FStar.Syntax.InstFV.fst"
let _37_52 = x
in (let _130_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _130_19}))
in ((_130_20), (imp)))
end))))
in (
# 52 "FStar.Syntax.InstFV.fst"
let body = (inst s body)
in (let _130_23 = (let _130_22 = (let _130_21 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_130_21)))
in FStar_Syntax_Syntax.Tm_abs (_130_22))
in (mk _130_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 56 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _130_26 = (
# 56 "FStar.Syntax.InstFV.fst"
let _37_63 = x
in (let _130_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _130_25}))
in ((_130_26), (imp)))
end))))
in (
# 57 "FStar.Syntax.InstFV.fst"
let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(
# 61 "FStar.Syntax.InstFV.fst"
let bv = (
# 61 "FStar.Syntax.InstFV.fst"
let _37_71 = bv
in (let _130_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _130_27}))
in (
# 62 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _130_31 = (let _130_30 = (let _130_29 = (inst s t)
in (let _130_28 = (inst_args s args)
in ((_130_29), (_130_28))))
in FStar_Syntax_Syntax.Tm_app (_130_30))
in (mk _130_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(
# 69 "FStar.Syntax.InstFV.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _37_86 -> (match (_37_86) with
| (p, wopt, t) -> begin
(
# 70 "FStar.Syntax.InstFV.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _130_33 = (inst s w)
in Some (_130_33))
end)
in (
# 73 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (let _130_36 = (let _130_35 = (let _130_34 = (inst s t)
in ((_130_34), (pats)))
in FStar_Syntax_Syntax.Tm_match (_130_35))
in (mk _130_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _130_41 = (let _130_40 = (let _130_39 = (inst s t1)
in (let _130_38 = (let _130_37 = (inst s t2)
in FStar_Util.Inl (_130_37))
in ((_130_39), (_130_38), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_130_40))
in (mk _130_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _130_46 = (let _130_45 = (let _130_44 = (inst s t1)
in (let _130_43 = (let _130_42 = (inst_comp s c)
in FStar_Util.Inr (_130_42))
in ((_130_44), (_130_43), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (_130_45))
in (mk _130_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(
# 84 "FStar.Syntax.InstFV.fst"
let lbs = (let _130_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 84 "FStar.Syntax.InstFV.fst"
let _37_110 = lb
in (let _130_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _130_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _130_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _130_48}))))))
in (((Prims.fst lbs)), (_130_50)))
in (let _130_53 = (let _130_52 = (let _130_51 = (inst s t)
in ((lbs), (_130_51)))
in FStar_Syntax_Syntax.Tm_let (_130_52))
in (mk _130_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _130_58 = (let _130_57 = (let _130_56 = (inst s t)
in (let _130_55 = (let _130_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_130_54))
in ((_130_56), (_130_55))))
in FStar_Syntax_Syntax.Tm_meta (_130_57))
in (mk _130_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(let _130_64 = (let _130_63 = (let _130_62 = (inst s t)
in (let _130_61 = (let _130_60 = (let _130_59 = (inst s t')
in ((m), (_130_59)))
in FStar_Syntax_Syntax.Meta_monadic (_130_60))
in ((_130_62), (_130_61))))
in FStar_Syntax_Syntax.Tm_meta (_130_63))
in (mk _130_64))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _130_67 = (let _130_66 = (let _130_65 = (inst s t)
in ((_130_65), (tag)))
in FStar_Syntax_Syntax.Tm_meta (_130_66))
in (mk _130_67))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_133 -> (match (_37_133) with
| (a, imp) -> begin
(let _130_71 = (inst s a)
in ((_130_71), (imp)))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _130_74 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _130_74))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _130_75 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _130_75))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 101 "FStar.Syntax.InstFV.fst"
let ct = (
# 101 "FStar.Syntax.InstFV.fst"
let _37_142 = ct
in (let _130_80 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _130_79 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _130_78 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _130_77 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_130_77))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _37_142.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _130_80; FStar_Syntax_Syntax.effect_args = _130_79; FStar_Syntax_Syntax.flags = _130_78}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _130_87 = (let _130_86 = (
# 113 "FStar.Syntax.InstFV.fst"
let _37_159 = lc
in (let _130_85 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_159.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _130_85; FStar_Syntax_Syntax.cflags = _37_159.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_161 -> (match (()) with
| () -> begin
(let _130_84 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _130_84))
end))}))
in FStar_Util.Inl (_130_86))
in Some (_130_87))
end))

# 114 "FStar.Syntax.InstFV.fst"
let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_166 -> begin
(inst i t)
end))




