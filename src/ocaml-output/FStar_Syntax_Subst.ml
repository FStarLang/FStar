
open Prims

let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _35_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _35_17 -> begin
t
end)
end
| _35_19 -> begin
t
end))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (let _126_8 = (c ())
in (force_delayed_thunk _126_8))
in (

let _35_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_32 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _35_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_39 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _35_46 -> begin
u
end)
end
| _35_48 -> begin
u
end))


let subst_to_string = (fun s -> (let _126_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _126_15 (FStar_String.concat ", "))))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _126_23 = (let _126_22 = (let _126_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _126_21))
in (FStar_Syntax_Syntax.bv_to_name _126_22))
in Some (_126_23))
end
| _35_62 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _126_29 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_70 = a
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_126_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _35_77 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _35_86 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _35_95 -> begin
None
end))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| (s0)::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some ((rest, st))
end)
end))


let map_some_curry = (fun f x _35_5 -> (match (_35_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _126_67 = (apply_until_some f s)
in (FStar_All.pipe_right _126_67 (map_some_curry g t))))


let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (

let u = (compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(apply_until_some_then_map (subst_univ_bv x) s subst_univ u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(apply_until_some_then_map (subst_univ_nm x) s subst_univ u)
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _126_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_126_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _126_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_126_73))
end)))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _35_139 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_159), _35_162) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _126_89 = (let _126_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_126_88))
in (FStar_Syntax_Syntax.mk _126_89 None t0.FStar_Syntax_Syntax.pos))
end
| _35_172 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _126_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_126_94))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _35_185 -> begin
(

let _35_186 = t
in (let _126_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _126_100 = (FStar_List.map (fun _35_190 -> (match (_35_190) with
| (t, imp) -> begin
(let _126_98 = (subst' s t)
in (_126_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _126_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_186.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _126_101; FStar_Syntax_Syntax.effect_args = _126_100; FStar_Syntax_Syntax.flags = _126_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _35_197 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _126_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _126_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _126_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _126_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _126_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _126_106))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))


let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB (((i + n), t))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN (((i + n), t))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM ((x, (i + n)))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD ((x, (i + n)))
end
| FStar_Syntax_Syntax.NT (_35_225) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))


let subst_binder' = (fun s _35_234 -> (match (_35_234) with
| (x, imp) -> begin
(let _126_124 = (

let _35_235 = x
in (let _126_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_123}))
in (_126_124, imp))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _126_129 = (shift_subst' i s)
in (subst_binder' _126_129 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' ((s)::[]) bs))


let subst_arg' = (fun s _35_246 -> (match (_35_246) with
| (t, imp) -> begin
(let _126_136 = (subst' s t)
in (_126_136, imp))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_256) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_264 = (aux n p)
in (match (_35_264) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _126_149 = (aux n p)
in (Prims.fst _126_149))) ps)
in ((

let _35_267 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_267.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_267.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_284 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_275 _35_278 -> (match ((_35_275, _35_278)) with
| ((pats, n), (p, imp)) -> begin
(

let _35_281 = (aux n p)
in (match (_35_281) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_284) with
| (pats, n) -> begin
((

let _35_285 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_285.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_285.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_290 = x
in (let _126_152 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_152}))
in ((

let _35_293 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_293.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_293.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_298 = x
in (let _126_153 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_298.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_298.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_153}))
in ((

let _35_301 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_301.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_301.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_308 = x
in (let _126_154 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_308.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_308.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_154}))
in (

let t0 = (subst' s t0)
in ((

let _35_312 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_312.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_312.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _126_161 = (let _126_160 = (

let _35_324 = l
in (let _126_159 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_324.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _126_159; FStar_Syntax_Syntax.cflags = _35_324.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_326 -> (match (()) with
| () -> begin
(let _126_158 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _126_158))
end))}))
in FStar_Util.Inl (_126_160))
in Some (_126_161))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_330) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _126_172 = (let _126_171 = (let _126_170 = (subst' s t0)
in (let _126_169 = (subst_args' s args)
in (_126_170, _126_169)))
in FStar_Syntax_Syntax.Tm_app (_126_171))
in (FStar_Syntax_Syntax.mk _126_172 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _126_177 = (let _126_176 = (let _126_175 = (subst' s t0)
in (let _126_174 = (let _126_173 = (subst' s t1)
in FStar_Util.Inl (_126_173))
in (_126_175, _126_174, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_126_176))
in (FStar_Syntax_Syntax.mk _126_177 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _126_182 = (let _126_181 = (let _126_180 = (subst' s t0)
in (let _126_179 = (let _126_178 = (subst_comp' s c)
in FStar_Util.Inr (_126_178))
in (_126_180, _126_179, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_126_181))
in (FStar_Syntax_Syntax.mk _126_182 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _126_187 = (let _126_186 = (let _126_185 = (subst_binders' s bs)
in (let _126_184 = (subst' s' body)
in (let _126_183 = (push_subst_lcomp s' lopt)
in (_126_185, _126_184, _126_183))))
in FStar_Syntax_Syntax.Tm_abs (_126_186))
in (FStar_Syntax_Syntax.mk _126_187 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _126_192 = (let _126_191 = (let _126_190 = (subst_binders' s bs)
in (let _126_189 = (let _126_188 = (shift_subst' n s)
in (subst_comp' _126_188 comp))
in (_126_190, _126_189)))
in FStar_Syntax_Syntax.Tm_arrow (_126_191))
in (FStar_Syntax_Syntax.mk _126_192 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_388 = x
in (let _126_193 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_388.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_388.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_193}))
in (

let phi = (let _126_194 = (shift_subst' 1 s)
in (subst' _126_194 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_400 -> (match (_35_400) with
| (pat, wopt, branch) -> begin
(

let _35_403 = (subst_pat' s pat)
in (match (_35_403) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _126_196 = (subst' s w)
in Some (_126_196))
end)
in (

let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(

let n = (FStar_List.length lbs)
in (

let sn = (shift_subst' n s)
in (

let body = (subst' sn body)
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let _35_425 = x
in {FStar_Syntax_Syntax.ppname = _35_425.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_425.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _35_429 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _35_431 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_431.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_431.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_429.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_429.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _35_434 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_434.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_434.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _126_202 = (let _126_201 = (let _126_200 = (subst' s t0)
in (let _126_199 = (let _126_198 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_126_198))
in (_126_200, _126_199)))
in FStar_Syntax_Syntax.Tm_meta (_126_201))
in (FStar_Syntax_Syntax.mk _126_202 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _126_205 = (let _126_204 = (let _126_203 = (subst' s t)
in (_126_203, m))
in FStar_Syntax_Syntax.Tm_meta (_126_204))
in (FStar_Syntax_Syntax.mk _126_205 None t.FStar_Syntax_Syntax.pos))
end))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _126_208 = (push_subst s t)
in (compress _126_208))
in (

let _35_456 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_459 -> begin
(force_uvar t)
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))


let closing_subst = (fun bs -> (let _126_220 = (FStar_List.fold_right (fun _35_468 _35_471 -> (match ((_35_468, _35_471)) with
| ((x, _35_467), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _126_220 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _35_482 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _126_226 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_482.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_482.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_226}))
in (

let o = (let _126_227 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_126_227)
in (

let _35_488 = (aux bs' o)
in (match (_35_488) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _126_230 = (open_binders' bs)
in (Prims.fst _126_230)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_494 = (open_binders' bs)
in (match (_35_494) with
| (bs', opening) -> begin
(let _126_235 = (subst opening t)
in (bs', _126_235, opening))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_501 = (open_term' bs t)
in (match (_35_501) with
| (b, t, _35_500) -> begin
(b, t)
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_506 = (open_binders' bs)
in (match (_35_506) with
| (bs', opening) -> begin
(let _126_244 = (subst_comp opening t)
in (bs', _126_244))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_513) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_516) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_522 = p
in (let _126_257 = (let _126_256 = (let _126_255 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_526 -> (match (_35_526) with
| (p, b) -> begin
(let _126_254 = (aux_disj sub renaming p)
in (_126_254, b))
end))))
in (fv, _126_255))
in FStar_Syntax_Syntax.Pat_cons (_126_256))
in {FStar_Syntax_Syntax.v = _126_257; FStar_Syntax_Syntax.ty = _35_522.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_522.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_534 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_537 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _126_259 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_537.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_537.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_259}))
end
| Some (y) -> begin
y
end)
in (

let _35_542 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_542.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_542.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_546 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _126_260 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_546.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_546.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_260}))
in (

let _35_549 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_549.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_549.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_555 = x
in (let _126_261 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_555.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_555.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_261}))
in (

let t0 = (subst sub t0)
in (

let _35_559 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_559.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_559.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_568) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_577 = (aux sub renaming p)
in (match (_35_577) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((

let _35_579 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_579.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_579.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_599 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_588 _35_591 -> (match ((_35_588, _35_591)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_595 = (aux sub renaming p)
in (match (_35_595) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_35_599) with
| (pats, sub, renaming) -> begin
((

let _35_600 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_600.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_600.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_604 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _126_270 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_604.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_604.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_270}))
in (

let sub = (let _126_271 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_126_271)
in ((

let _35_608 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_608.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_608.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_612 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _126_272 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_612.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_612.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_272}))
in (

let sub = (let _126_273 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_126_273)
in ((

let _35_616 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_616.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_616.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_622 = x
in (let _126_274 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_622.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_622.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_274}))
in (

let t0 = (subst sub t0)
in ((

let _35_626 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_626.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_626.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (

let _35_632 = (aux [] [] p)
in (match (_35_632) with
| (p, sub, _35_631) -> begin
(p, sub)
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_636 -> (match (_35_636) with
| (p, wopt, e) -> begin
(

let _35_639 = (open_pat p)
in (match (_35_639) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _126_277 = (subst opening w)
in Some (_126_277))
end)
in (

let e = (subst opening e)
in (p, wopt, e)))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _126_282 = (closing_subst bs)
in (subst _126_282 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _126_287 = (closing_subst bs)
in (subst_comp _126_287 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _35_659 = x
in (let _126_294 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_659.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_659.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_294}))
in (

let s' = (let _126_295 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_126_295)
in (let _126_296 = (aux s' tl)
in ((x, imp))::_126_296)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_666 = lc
in (let _126_303 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_666.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _126_303; FStar_Syntax_Syntax.cflags = _35_666.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_668 -> (match (()) with
| () -> begin
(let _126_302 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _126_302))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_676) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_684 = (aux sub p)
in (match (_35_684) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _126_311 = (aux sub p)
in (Prims.fst _126_311))) ps)
in ((

let _35_687 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_687.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_687.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_704 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_695 _35_698 -> (match ((_35_695, _35_698)) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_701 = (aux sub p)
in (match (_35_701) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_704) with
| (pats, sub) -> begin
((

let _35_705 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_705.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_705.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_709 = x
in (let _126_314 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_709.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_709.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_314}))
in (

let sub = (let _126_315 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_126_315)
in ((

let _35_713 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_713.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_713.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_717 = x
in (let _126_316 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_717.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_717.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_316}))
in (

let sub = (let _126_317 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_126_317)
in ((

let _35_721 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_721.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_721.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_727 = x
in (let _126_318 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_727.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_727.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _126_318}))
in (

let t0 = (subst sub t0)
in ((

let _35_731 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_731.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_731.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_736 -> (match (_35_736) with
| (p, wopt, e) -> begin
(

let _35_739 = (close_pat p)
in (match (_35_739) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _126_321 = (subst closing w)
in Some (_126_321))
end)
in (

let e = (subst closing e)
in (p, wopt, e)))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - 1)
in (

let _35_752 = (let _126_326 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _126_326 FStar_List.unzip))
in (match (_35_752) with
| (s, us') -> begin
(s, us')
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_757 = (univ_var_opening us)
in (match (_35_757) with
| (s, us') -> begin
(

let t = (subst s t)
in (us', t))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_763 = (univ_var_opening us)
in (match (_35_763) with
| (s, us') -> begin
(let _126_335 = (subst_comp s c)
in (us', _126_335))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n = ((FStar_List.length us) - 1)
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n = ((FStar_List.length us) - 1)
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(

let _35_789 = (FStar_List.fold_right (fun lb _35_782 -> (match (_35_782) with
| (i, lbs, out) -> begin
(

let x = (let _126_354 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _126_354))
in ((i + 1), ((

let _35_784 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_784.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_784.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_784.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_784.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.DB ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_35_789) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_801 = (FStar_List.fold_right (fun u _35_795 -> (match (_35_795) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UN ((i, FStar_Syntax_Syntax.U_name (u))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_35_801) with
| (_35_798, us, u_let_rec_opening) -> begin
(

let _35_802 = lb
in (let _126_358 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_802.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_802.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_802.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _126_358}))
end)))))
in (

let t = (subst let_rec_opening t)
in (lbs, t)))
end))
end)


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(

let _35_814 = (FStar_List.fold_right (fun lb _35_811 -> (match (_35_811) with
| (i, out) -> begin
(let _126_368 = (let _126_367 = (let _126_366 = (let _126_365 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_126_365, i))
in FStar_Syntax_Syntax.NM (_126_366))
in (_126_367)::out)
in ((i + 1), _126_368))
end)) lbs (0, []))
in (match (_35_814) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_823 = (FStar_List.fold_right (fun u _35_819 -> (match (_35_819) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UD ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_35_823) with
| (_35_821, u_let_rec_closing) -> begin
(

let _35_824 = lb
in (let _126_372 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_824.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_824.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_824.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_824.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _126_372}))
end)))))
in (

let t = (subst let_rec_closing t)
in (lbs, t)))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_831 -> (match (_35_831) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - 1)
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_838 -> (match (_35_838) with
| (x, _35_837) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (

let t = (subst s t)
in (us, t)))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_844 -> (match (_35_844) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - 1)
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _126_385 = (subst s t)
in (us', _126_385)))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_856 -> (match (_35_856) with
| (x, _35_855) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




