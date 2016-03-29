
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
let mk = (fun s -> (let _106_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _106_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_27_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _27_37 -> (match (_27_37) with
| (x, _27_36) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_27_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 51 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _27_51 -> (match (_27_51) with
| (x, imp) -> begin
(let _106_20 = (
# 51 "FStar.Syntax.InstFV.fst"
let _27_52 = x
in (let _106_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _27_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _27_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _106_19}))
in (_106_20, imp))
end))))
in (
# 52 "FStar.Syntax.InstFV.fst"
let body = (inst s body)
in (let _106_23 = (let _106_22 = (let _106_21 = (inst_lcomp_opt s lopt)
in (bs, body, _106_21))
in FStar_Syntax_Syntax.Tm_abs (_106_22))
in (mk _106_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 56 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _27_62 -> (match (_27_62) with
| (x, imp) -> begin
(let _106_26 = (
# 56 "FStar.Syntax.InstFV.fst"
let _27_63 = x
in (let _106_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _27_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _27_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _106_25}))
in (_106_26, imp))
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
let _27_71 = bv
in (let _106_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _27_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _27_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _106_27}))
in (
# 62 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _106_31 = (let _106_30 = (let _106_29 = (inst s t)
in (let _106_28 = (inst_args s args)
in (_106_29, _106_28)))
in FStar_Syntax_Syntax.Tm_app (_106_30))
in (mk _106_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(
# 69 "FStar.Syntax.InstFV.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _27_86 -> (match (_27_86) with
| (p, wopt, t) -> begin
(
# 70 "FStar.Syntax.InstFV.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _106_33 = (inst s w)
in Some (_106_33))
end)
in (
# 73 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _106_36 = (let _106_35 = (let _106_34 = (inst s t)
in (_106_34, pats))
in FStar_Syntax_Syntax.Tm_match (_106_35))
in (mk _106_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _106_41 = (let _106_40 = (let _106_39 = (inst s t1)
in (let _106_38 = (let _106_37 = (inst s t2)
in FStar_Util.Inl (_106_37))
in (_106_39, _106_38, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_106_40))
in (mk _106_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _106_46 = (let _106_45 = (let _106_44 = (inst s t1)
in (let _106_43 = (let _106_42 = (inst_comp s c)
in FStar_Util.Inr (_106_42))
in (_106_44, _106_43, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_106_45))
in (mk _106_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(
# 84 "FStar.Syntax.InstFV.fst"
let lbs = (let _106_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 84 "FStar.Syntax.InstFV.fst"
let _27_110 = lb
in (let _106_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _106_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _27_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _27_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _106_49; FStar_Syntax_Syntax.lbeff = _27_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _106_48}))))))
in ((Prims.fst lbs), _106_50))
in (let _106_53 = (let _106_52 = (let _106_51 = (inst s t)
in (lbs, _106_51))
in FStar_Syntax_Syntax.Tm_let (_106_52))
in (mk _106_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _106_58 = (let _106_57 = (let _106_56 = (inst s t)
in (let _106_55 = (let _106_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_106_54))
in (_106_56, _106_55)))
in FStar_Syntax_Syntax.Tm_meta (_106_57))
in (mk _106_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _106_61 = (let _106_60 = (let _106_59 = (inst s t)
in (_106_59, tag))
in FStar_Syntax_Syntax.Tm_meta (_106_60))
in (mk _106_61))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _27_126 -> (match (_27_126) with
| (a, imp) -> begin
(let _106_65 = (inst s a)
in (_106_65, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _106_68 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _106_68))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _106_69 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _106_69))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 98 "FStar.Syntax.InstFV.fst"
let ct = (
# 98 "FStar.Syntax.InstFV.fst"
let _27_135 = ct
in (let _106_74 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _106_73 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _106_72 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _27_1 -> (match (_27_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _106_71 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_106_71))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _27_135.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _106_74; FStar_Syntax_Syntax.effect_args = _106_73; FStar_Syntax_Syntax.flags = _106_72}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _106_80 = (
# 109 "FStar.Syntax.InstFV.fst"
let _27_147 = lc
in (let _106_79 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _27_147.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _106_79; FStar_Syntax_Syntax.cflags = _27_147.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _27_149 -> (match (()) with
| () -> begin
(let _106_78 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _106_78))
end))}))
in Some (_106_80))
end))

# 112 "FStar.Syntax.InstFV.fst"
let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _27_154 -> begin
(inst i t)
end))




