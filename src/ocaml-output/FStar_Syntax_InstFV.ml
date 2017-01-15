
open Prims

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk = (fun t s -> (let _0_224 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk s _0_224 t.FStar_Syntax_Syntax.pos)))


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
in (mk (FStar_Syntax_Syntax.Tm_abs ((let _0_225 = (inst_lcomp_opt s lopt)
in ((bs), (body), (_0_225))))))))
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

let uu___172_208 = bv
in (let _0_226 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___172_208.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___172_208.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_226}))
in (

let t = (inst s t)
in (mk (FStar_Syntax_Syntax.Tm_refine (((bv), (t)))))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_228 = (inst s t)
in (let _0_227 = (inst_args s args)
in ((_0_228), (_0_227)))))))
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
in (mk (FStar_Syntax_Syntax.Tm_match ((let _0_229 = (inst s t)
in ((_0_229), (pats)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), f) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_231 = (inst s t1)
in (let _0_230 = FStar_Util.Inl ((inst s t2))
in ((_0_231), (_0_230), (f)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), f) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_233 = (inst s t1)
in (let _0_232 = FStar_Util.Inr ((inst_comp s c))
in ((_0_233), (_0_232), (f)))))))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let lbs = (let _0_236 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu___173_416 = lb
in (let _0_235 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_234 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___173_416.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___173_416.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_235; FStar_Syntax_Syntax.lbeff = uu___173_416.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_234}))))))
in (((Prims.fst lbs)), (_0_236)))
in (mk (FStar_Syntax_Syntax.Tm_let ((let _0_237 = (inst s t)
in ((lbs), (_0_237)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_239 = (inst s t)
in (let _0_238 = FStar_Syntax_Syntax.Meta_pattern ((FStar_All.pipe_right args (FStar_List.map (inst_args s))))
in ((_0_239), (_0_238)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_242 = (inst s t)
in (let _0_241 = FStar_Syntax_Syntax.Meta_monadic ((let _0_240 = (inst s t')
in ((m), (_0_240))))
in ((_0_242), (_0_241)))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, tag) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_243 = (inst s t)
in ((_0_243), (tag))))))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____484 -> (match (uu____484) with
| (x, imp) -> begin
(let _0_245 = (

let uu___174_491 = x
in (let _0_244 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___174_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___174_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_244}))
in ((_0_245), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____515 -> (match (uu____515) with
| (a, imp) -> begin
(let _0_246 = (inst s a)
in ((_0_246), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _0_247 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' _0_247 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _0_248 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' _0_248 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct = (

let uu___175_550 = ct
in (let _0_251 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (let _0_250 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (let _0_249 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___171_553 -> (match (uu___171_553) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
FStar_Syntax_Syntax.DECREASES ((inst s t))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___175_550.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___175_550.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _0_251; FStar_Syntax_Syntax.effect_args = _0_250; FStar_Syntax_Syntax.flags = _0_249}))))
in (FStar_Syntax_Syntax.mk_Comp ct))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun s l -> (match (l) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
l
end
| Some (FStar_Util.Inl (lc)) -> begin
Some (FStar_Util.Inl ((

let uu___176_607 = lc
in (let _0_253 = (inst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = uu___176_607.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _0_253; FStar_Syntax_Syntax.cflags = uu___176_607.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____608 -> (let _0_252 = (lc.FStar_Syntax_Syntax.comp ())
in (inst_comp s _0_252)))}))))
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




