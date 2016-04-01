
open Prims
# 25 "FStar.Syntax.InstFV.fst"
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

# 29 "FStar.Syntax.InstFV.fst"
let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (
# 30 "FStar.Syntax.InstFV.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 31 "FStar.Syntax.InstFV.fst"
let mk = (fun s -> (let _126_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _126_13 t.FStar_Syntax_Syntax.pos)))
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
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 51 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_51 -> (match (_37_51) with
| (x, imp) -> begin
(let _126_20 = (
# 51 "FStar.Syntax.InstFV.fst"
let _37_52 = x
in (let _126_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_19}))
in (_126_20, imp))
end))))
in (
# 52 "FStar.Syntax.InstFV.fst"
let body = (inst s body)
in (let _126_23 = (let _126_22 = (let _126_21 = (inst_lcomp_opt s lopt)
in (bs, body, _126_21))
in FStar_Syntax_Syntax.Tm_abs (_126_22))
in (mk _126_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 56 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _37_62 -> (match (_37_62) with
| (x, imp) -> begin
(let _126_26 = (
# 56 "FStar.Syntax.InstFV.fst"
let _37_63 = x
in (let _126_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_25}))
in (_126_26, imp))
end))))
in (
# 57 "FStar.Syntax.InstFV.fst"
let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(
# 61 "FStar.Syntax.InstFV.fst"
let bv = (
# 61 "FStar.Syntax.InstFV.fst"
let _37_71 = bv
in (let _126_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _37_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _37_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_27}))
in (
# 62 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _126_31 = (let _126_30 = (let _126_29 = (inst s t)
in (let _126_28 = (inst_args s args)
in (_126_29, _126_28)))
in FStar_Syntax_Syntax.Tm_app (_126_30))
in (mk _126_31))
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
(let _126_33 = (inst s w)
in Some (_126_33))
end)
in (
# 73 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _126_36 = (let _126_35 = (let _126_34 = (inst s t)
in (_126_34, pats))
in FStar_Syntax_Syntax.Tm_match (_126_35))
in (mk _126_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _126_41 = (let _126_40 = (let _126_39 = (inst s t1)
in (let _126_38 = (let _126_37 = (inst s t2)
in FStar_Util.Inl (_126_37))
in (_126_39, _126_38, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_126_40))
in (mk _126_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _126_46 = (let _126_45 = (let _126_44 = (inst s t1)
in (let _126_43 = (let _126_42 = (inst_comp s c)
in FStar_Util.Inr (_126_42))
in (_126_44, _126_43, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_126_45))
in (mk _126_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(
# 84 "FStar.Syntax.InstFV.fst"
let lbs = (let _126_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 84 "FStar.Syntax.InstFV.fst"
let _37_110 = lb
in (let _126_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _126_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _37_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _37_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _126_49; FStar_Syntax_Syntax.lbeff = _37_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _126_48}))))))
in ((Prims.fst lbs), _126_50))
in (let _126_53 = (let _126_52 = (let _126_51 = (inst s t)
in (lbs, _126_51))
in FStar_Syntax_Syntax.Tm_let (_126_52))
in (mk _126_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _126_58 = (let _126_57 = (let _126_56 = (inst s t)
in (let _126_55 = (let _126_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_126_54))
in (_126_56, _126_55)))
in FStar_Syntax_Syntax.Tm_meta (_126_57))
in (mk _126_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _126_61 = (let _126_60 = (let _126_59 = (inst s t)
in (_126_59, tag))
in FStar_Syntax_Syntax.Tm_meta (_126_60))
in (mk _126_61))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _37_126 -> (match (_37_126) with
| (a, imp) -> begin
(let _126_65 = (inst s a)
in (_126_65, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _126_68 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _126_68))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _126_69 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _126_69))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 98 "FStar.Syntax.InstFV.fst"
let ct = (
# 98 "FStar.Syntax.InstFV.fst"
let _37_135 = ct
in (let _126_74 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _126_73 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _126_72 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _37_1 -> (match (_37_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _126_71 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_126_71))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _37_135.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _126_74; FStar_Syntax_Syntax.effect_args = _126_73; FStar_Syntax_Syntax.flags = _126_72}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _126_80 = (
# 109 "FStar.Syntax.InstFV.fst"
let _37_147 = lc
in (let _126_79 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _37_147.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _126_79; FStar_Syntax_Syntax.cflags = _37_147.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _37_149 -> (match (()) with
| () -> begin
(let _126_78 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _126_78))
end))}))
in Some (_126_80))
end))

# 112 "FStar.Syntax.InstFV.fst"
let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _37_154 -> begin
(inst i t)
end))




