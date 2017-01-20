
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (let _0_139 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _0_139 t.FStar_Syntax_Syntax.pos)))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let mk = (mk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____121) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uinst (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(s t fv)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs = (inst_binders s bs)
in (

let body = (inst s body)
in (mk (FStar_Syntax_Syntax.Tm_abs ((let _0_140 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_0_140))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (inst_binders s bs)
in (

let c = (inst_comp s c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let bv = (

let uu___158_208 = bv
in (let _0_141 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___158_208.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_208.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_141}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_143 = (inst s t)
in (let _0_142 = (inst_args s args)
in ((_0_143), (_0_142)))))))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____297 -> (match (uu____297) with
| (p, wopt, t) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((inst s w))
end)
in (

let t = (inst s t)
in ((p), (wopt), (t))))
end))))
in (mk (FStar_Syntax_Syntax.Tm_match ((let _0_144 = (inst s t)
in ((_0_144), (pats)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_146 = (inst s t1)
in (let _0_145 = FStar_Util.Inl ((inst s t2))
in ((_0_146), (_0_145), (f)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_148 = (inst s t1)
in (let _0_147 = FStar_Util.Inr ((inst_comp s c))
in ((_0_148), (_0_147), (f)))))))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _0_151 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu___159_416 = lb
in (let _0_150 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_149 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___159_416.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___159_416.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_150; FStar_Syntax_Syntax.lbeff = uu___159_416.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_149}))))))
in (((Prims.fst lbs)), (_0_151)))
in (mk (FStar_Syntax_Syntax.Tm_let ((let _0_152 = (inst s t)
in ((lbs), (_0_152)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_154 = (inst s t)
in (let _0_153 = FStar_Syntax_Syntax.Meta_pattern ((FStar_All.pipe_right args (FStar_List.map (inst_args s))))
in ((_0_154), (_0_153)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_157 = (inst s t)
in (let _0_156 = FStar_Syntax_Syntax.Meta_monadic ((let _0_155 = (inst s t')
in ((m), (_0_155))))
in ((_0_157), (_0_156)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_158 = (inst s t)
in ((_0_158), (tag))))))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____484 -> (match (uu____484) with
| (x, imp) -> begin
(let _0_160 = (

let uu___160_491 = x
in (let _0_159 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___160_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_159}))
in ((_0_160), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____515 -> (match (uu____515) with
| (a, imp) -> begin
(let _0_161 = (inst s a)
in ((_0_161), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _0_162 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _0_162 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _0_163 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _0_163 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let uu___161_550 = ct
in (let _0_166 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _0_165 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _0_164 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___157_553 -> (match (uu___157_553) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
FStar_Syntax_Syntax.DECREASES ((inst s t))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___161_550.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___161_550.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _0_166; FStar_Syntax_Syntax.effect_args = _0_165; FStar_Syntax_Syntax.flags = _0_164}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
Some (FStar_Util.Inl ((

let uu___162_607 = lc
in (let _0_168 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___162_607.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_168; FStar_Syntax_Syntax.cflags = uu___162_607.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____608 -> (let _0_167 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _0_167)))}))))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____617 -> begin
(

let inst_fv = (fun t fv -> (

let uu____625 = (FStar_Util.find_opt (fun uu____631 -> (match (uu____631) with
| (x, uu____635) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____625) with
| None -> begin
t
end
| Some (uu____642, us) -> begin
(mk t (FStar_Syntax_Syntax.Tm_uinst (((t), (us)))))
end)))
in (inst inst_fv t))
end))




