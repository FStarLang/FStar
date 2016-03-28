
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
let mk = (fun s -> (let _118_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _118_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_33_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _33_37 -> (match (_33_37) with
| (x, _33_36) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_33_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 51 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _33_51 -> (match (_33_51) with
| (x, imp) -> begin
(let _118_20 = (
# 51 "FStar.Syntax.InstFV.fst"
let _33_52 = x
in (let _118_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _33_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _33_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _118_19}))
in (_118_20, imp))
end))))
in (
# 52 "FStar.Syntax.InstFV.fst"
let body = (inst s body)
in (let _118_23 = (let _118_22 = (let _118_21 = (inst_lcomp_opt s lopt)
in (bs, body, _118_21))
in FStar_Syntax_Syntax.Tm_abs (_118_22))
in (mk _118_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 56 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _33_62 -> (match (_33_62) with
| (x, imp) -> begin
(let _118_26 = (
# 56 "FStar.Syntax.InstFV.fst"
let _33_63 = x
in (let _118_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _33_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _33_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _118_25}))
in (_118_26, imp))
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
let _33_71 = bv
in (let _118_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _33_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _33_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _118_27}))
in (
# 62 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _118_31 = (let _118_30 = (let _118_29 = (inst s t)
in (let _118_28 = (inst_args s args)
in (_118_29, _118_28)))
in FStar_Syntax_Syntax.Tm_app (_118_30))
in (mk _118_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(
# 69 "FStar.Syntax.InstFV.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _33_86 -> (match (_33_86) with
| (p, wopt, t) -> begin
(
# 70 "FStar.Syntax.InstFV.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _118_33 = (inst s w)
in Some (_118_33))
end)
in (
# 73 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _118_36 = (let _118_35 = (let _118_34 = (inst s t)
in (_118_34, pats))
in FStar_Syntax_Syntax.Tm_match (_118_35))
in (mk _118_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(let _118_41 = (let _118_40 = (let _118_39 = (inst s t1)
in (let _118_38 = (let _118_37 = (inst s t2)
in FStar_Util.Inl (_118_37))
in (_118_39, _118_38, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_118_40))
in (mk _118_41))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(let _118_46 = (let _118_45 = (let _118_44 = (inst s t1)
in (let _118_43 = (let _118_42 = (inst_comp s c)
in FStar_Util.Inr (_118_42))
in (_118_44, _118_43, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_118_45))
in (mk _118_46))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(
# 84 "FStar.Syntax.InstFV.fst"
let lbs = (let _118_50 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 84 "FStar.Syntax.InstFV.fst"
let _33_110 = lb
in (let _118_49 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _118_48 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _33_110.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _33_110.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _118_49; FStar_Syntax_Syntax.lbeff = _33_110.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _118_48}))))))
in ((Prims.fst lbs), _118_50))
in (let _118_53 = (let _118_52 = (let _118_51 = (inst s t)
in (lbs, _118_51))
in FStar_Syntax_Syntax.Tm_let (_118_52))
in (mk _118_53)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _118_58 = (let _118_57 = (let _118_56 = (inst s t)
in (let _118_55 = (let _118_54 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_118_54))
in (_118_56, _118_55)))
in FStar_Syntax_Syntax.Tm_meta (_118_57))
in (mk _118_58))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _118_61 = (let _118_60 = (let _118_59 = (inst s t)
in (_118_59, tag))
in FStar_Syntax_Syntax.Tm_meta (_118_60))
in (mk _118_61))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _33_126 -> (match (_33_126) with
| (a, imp) -> begin
(let _118_65 = (inst s a)
in (_118_65, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _118_68 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _118_68))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _118_69 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _118_69))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 98 "FStar.Syntax.InstFV.fst"
let ct = (
# 98 "FStar.Syntax.InstFV.fst"
let _33_135 = ct
in (let _118_74 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _118_73 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _118_72 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _33_1 -> (match (_33_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _118_71 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_118_71))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _33_135.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _118_74; FStar_Syntax_Syntax.effect_args = _118_73; FStar_Syntax_Syntax.flags = _118_72}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _118_80 = (
# 109 "FStar.Syntax.InstFV.fst"
let _33_147 = lc
in (let _118_79 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _33_147.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _118_79; FStar_Syntax_Syntax.cflags = _33_147.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _33_149 -> (match (()) with
| () -> begin
(let _118_78 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _118_78))
end))}))
in Some (_118_80))
end))

# 112 "FStar.Syntax.InstFV.fst"
let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _33_154 -> begin
(inst i t)
end))




