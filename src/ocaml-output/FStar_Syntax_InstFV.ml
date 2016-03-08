
open Prims
# 24 "FStar.Syntax.InstFV.fst"
type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list

# 28 "FStar.Syntax.InstFV.fst"
let rec inst : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (
# 29 "FStar.Syntax.InstFV.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 30 "FStar.Syntax.InstFV.fst"
let mk = (fun s -> (let _113_13 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _113_13 t.FStar_Syntax_Syntax.pos)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_34_8) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(match ((FStar_Util.find_opt (fun _34_37 -> (match (_34_37) with
| (x, _34_36) -> begin
(FStar_Ident.lid_equals x (Prims.fst fv).FStar_Syntax_Syntax.v)
end)) s)) with
| None -> begin
t
end
| Some (_34_40, us) -> begin
(mk (FStar_Syntax_Syntax.Tm_uinst ((t, us))))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 50 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _34_51 -> (match (_34_51) with
| (x, imp) -> begin
(let _113_20 = (
# 50 "FStar.Syntax.InstFV.fst"
let _34_52 = x
in (let _113_19 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_52.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_19}))
in (_113_20, imp))
end))))
in (
# 51 "FStar.Syntax.InstFV.fst"
let body = (inst s body)
in (let _113_23 = (let _113_22 = (let _113_21 = (inst_lcomp_opt s lopt)
in (bs, body, _113_21))
in FStar_Syntax_Syntax.Tm_abs (_113_22))
in (mk _113_23))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 55 "FStar.Syntax.InstFV.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.map (fun _34_62 -> (match (_34_62) with
| (x, imp) -> begin
(let _113_26 = (
# 55 "FStar.Syntax.InstFV.fst"
let _34_63 = x
in (let _113_25 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_63.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_63.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_25}))
in (_113_26, imp))
end))))
in (
# 56 "FStar.Syntax.InstFV.fst"
let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(
# 60 "FStar.Syntax.InstFV.fst"
let bv = (
# 60 "FStar.Syntax.InstFV.fst"
let _34_71 = bv
in (let _113_27 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_71.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_27}))
in (
# 61 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((bv, t))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _113_31 = (let _113_30 = (let _113_29 = (inst s t)
in (let _113_28 = (inst_args s args)
in (_113_29, _113_28)))
in FStar_Syntax_Syntax.Tm_app (_113_30))
in (mk _113_31))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(
# 68 "FStar.Syntax.InstFV.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _34_86 -> (match (_34_86) with
| (p, wopt, t) -> begin
(
# 69 "FStar.Syntax.InstFV.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _113_33 = (inst s w)
in Some (_113_33))
end)
in (
# 72 "FStar.Syntax.InstFV.fst"
let t = (inst s t)
in (p, wopt, t)))
end))))
in (let _113_36 = (let _113_35 = (let _113_34 = (inst s t)
in (_113_34, pats))
in FStar_Syntax_Syntax.Tm_match (_113_35))
in (mk _113_36)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, f) -> begin
(let _113_40 = (let _113_39 = (let _113_38 = (inst s t1)
in (let _113_37 = (inst s t2)
in (_113_38, _113_37, f)))
in FStar_Syntax_Syntax.Tm_ascribed (_113_39))
in (mk _113_40))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(
# 80 "FStar.Syntax.InstFV.fst"
let lbs = (let _113_44 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 80 "FStar.Syntax.InstFV.fst"
let _34_103 = lb
in (let _113_43 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _113_42 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _34_103.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _34_103.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _113_43; FStar_Syntax_Syntax.lbeff = _34_103.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _113_42}))))))
in ((Prims.fst lbs), _113_44))
in (let _113_47 = (let _113_46 = (let _113_45 = (inst s t)
in (lbs, _113_45))
in FStar_Syntax_Syntax.Tm_let (_113_46))
in (mk _113_47)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _113_52 = (let _113_51 = (let _113_50 = (inst s t)
in (let _113_49 = (let _113_48 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (_113_48))
in (_113_50, _113_49)))
in FStar_Syntax_Syntax.Tm_meta (_113_51))
in (mk _113_52))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(let _113_55 = (let _113_54 = (let _113_53 = (inst s t)
in (_113_53, tag))
in FStar_Syntax_Syntax.Tm_meta (_113_54))
in (mk _113_55))
end))))
and inst_args : inst_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun _34_119 -> (match (_34_119) with
| (a, imp) -> begin
(let _113_59 = (inst s a)
in (_113_59, imp))
end)))))
and inst_comp : inst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _113_62 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total _113_62))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _113_63 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal _113_63))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 94 "FStar.Syntax.InstFV.fst"
let ct = (
# 94 "FStar.Syntax.InstFV.fst"
let _34_128 = ct
in (let _113_68 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _113_67 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _113_66 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _34_1 -> (match (_34_1) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _113_65 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (_113_65))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.effect_name = _34_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _113_68; FStar_Syntax_Syntax.effect_args = _113_67; FStar_Syntax_Syntax.flags = _113_66}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : inst_t  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (lc) -> begin
(let _113_74 = (
# 105 "FStar.Syntax.InstFV.fst"
let _34_140 = lc
in (let _113_73 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _34_140.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _113_73; FStar_Syntax_Syntax.cflags = _34_140.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _34_142 -> (match (()) with
| () -> begin
(let _113_72 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _113_72))
end))}))
in Some (_113_74))
end))

# 108 "FStar.Syntax.InstFV.fst"
let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| _34_147 -> begin
(inst i t)
end))




