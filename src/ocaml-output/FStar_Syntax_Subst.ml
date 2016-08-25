
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

let t' = (let _128_8 = (c ())
in (force_delayed_thunk _128_8))
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


let subst_to_string = (fun s -> (let _128_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _128_15 (FStar_String.concat ", "))))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _128_23 = (let _128_22 = (let _128_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _128_21))
in (FStar_Syntax_Syntax.bv_to_name _128_22))
in Some (_128_23))
end
| _35_62 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _128_29 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_70 = a
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_128_29))
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
Some (((rest), (st)))
end)
end))


let map_some_curry = (fun f x _35_5 -> (match (_35_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _128_67 = (apply_until_some f s)
in (FStar_All.pipe_right _128_67 (map_some_curry g t))))


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
(let _128_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_128_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _128_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_128_73))
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
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((FStar_List.append s' s))))) t.FStar_Syntax_Syntax.pos)
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
(let _128_89 = (let _128_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_128_88))
in (FStar_Syntax_Syntax.mk _128_89 None t0.FStar_Syntax_Syntax.pos))
end
| _35_172 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _128_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_128_94))
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
in (let _128_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _128_100 = (FStar_List.map (fun _35_190 -> (match (_35_190) with
| (t, imp) -> begin
(let _128_98 = (subst' s t)
in ((_128_98), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _128_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_186.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _128_101; FStar_Syntax_Syntax.effect_args = _128_100; FStar_Syntax_Syntax.flags = _128_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _35_197 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _128_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _128_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _128_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _128_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _128_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _128_106))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))


let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM (((x), ((i + n))))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD (((x), ((i + n))))
end
| FStar_Syntax_Syntax.NT (_35_225) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))


let subst_binder' = (fun s _35_234 -> (match (_35_234) with
| (x, imp) -> begin
(let _128_124 = (

let _35_235 = x
in (let _128_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_123}))
in ((_128_124), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = (Prims.parse_int "0")) then begin
(subst_binder' s b)
end else begin
(let _128_129 = (shift_subst' i s)
in (subst_binder' _128_129 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' ((s)::[]) bs))


let subst_arg' = (fun s _35_246 -> (match (_35_246) with
| (t, imp) -> begin
(let _128_136 = (subst' s t)
in ((_128_136), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_256) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_264 = (aux n p)
in (match (_35_264) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _128_149 = (aux n p)
in (Prims.fst _128_149))) ps)
in (((

let _35_267 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_267.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_267.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_284 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_275 _35_278 -> (match (((_35_275), (_35_278))) with
| ((pats, n), (p, imp)) -> begin
(

let _35_281 = (aux n p)
in (match (_35_281) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (_35_284) with
| (pats, n) -> begin
(((

let _35_285 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_285.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_285.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_290 = x
in (let _128_152 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_152}))
in (((

let _35_293 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_293.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_293.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_298 = x
in (let _128_153 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_298.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_298.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_153}))
in (((

let _35_301 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_301.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_301.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_308 = x
in (let _128_154 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_308.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_308.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_154}))
in (

let t0 = (subst' s t0)
in (((

let _35_312 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_312.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_312.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _128_161 = (let _128_160 = (

let _35_324 = l
in (let _128_159 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_324.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _128_159; FStar_Syntax_Syntax.cflags = _35_324.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_326 -> (match (()) with
| () -> begin
(let _128_158 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _128_158))
end))}))
in FStar_Util.Inl (_128_160))
in Some (_128_161))
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
(let _128_172 = (let _128_171 = (let _128_170 = (subst' s t0)
in (let _128_169 = (subst_args' s args)
in ((_128_170), (_128_169))))
in FStar_Syntax_Syntax.Tm_app (_128_171))
in (FStar_Syntax_Syntax.mk _128_172 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _128_177 = (let _128_176 = (let _128_175 = (subst' s t0)
in (let _128_174 = (let _128_173 = (subst' s t1)
in FStar_Util.Inl (_128_173))
in ((_128_175), (_128_174), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_128_176))
in (FStar_Syntax_Syntax.mk _128_177 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _128_182 = (let _128_181 = (let _128_180 = (subst' s t0)
in (let _128_179 = (let _128_178 = (subst_comp' s c)
in FStar_Util.Inr (_128_178))
in ((_128_180), (_128_179), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_128_181))
in (FStar_Syntax_Syntax.mk _128_182 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _128_187 = (let _128_186 = (let _128_185 = (subst_binders' s bs)
in (let _128_184 = (subst' s' body)
in (let _128_183 = (push_subst_lcomp s' lopt)
in ((_128_185), (_128_184), (_128_183)))))
in FStar_Syntax_Syntax.Tm_abs (_128_186))
in (FStar_Syntax_Syntax.mk _128_187 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _128_192 = (let _128_191 = (let _128_190 = (subst_binders' s bs)
in (let _128_189 = (let _128_188 = (shift_subst' n s)
in (subst_comp' _128_188 comp))
in ((_128_190), (_128_189))))
in FStar_Syntax_Syntax.Tm_arrow (_128_191))
in (FStar_Syntax_Syntax.mk _128_192 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_388 = x
in (let _128_193 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_388.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_388.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_193}))
in (

let phi = (let _128_194 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _128_194 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))) None t.FStar_Syntax_Syntax.pos)))
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
(let _128_196 = (subst' s w)
in Some (_128_196))
end)
in (

let branch = (subst' s branch)
in ((pat), (wopt), (branch)))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t0), (pats)))) None t.FStar_Syntax_Syntax.pos)))
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
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _128_202 = (let _128_201 = (let _128_200 = (subst' s t0)
in (let _128_199 = (let _128_198 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_128_198))
in ((_128_200), (_128_199))))
in FStar_Syntax_Syntax.Tm_meta (_128_201))
in (FStar_Syntax_Syntax.mk _128_202 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(let _128_208 = (let _128_207 = (let _128_206 = (subst' s t0)
in (let _128_205 = (let _128_204 = (let _128_203 = (subst' s t)
in ((m), (_128_203)))
in FStar_Syntax_Syntax.Meta_monadic (_128_204))
in ((_128_206), (_128_205))))
in FStar_Syntax_Syntax.Tm_meta (_128_207))
in (FStar_Syntax_Syntax.mk _128_208 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _128_211 = (let _128_210 = (let _128_209 = (subst' s t)
in ((_128_209), (m)))
in FStar_Syntax_Syntax.Tm_meta (_128_210))
in (FStar_Syntax_Syntax.mk _128_211 None t.FStar_Syntax_Syntax.pos))
end))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _128_214 = (push_subst s t)
in (compress _128_214))
in (

let _35_463 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_466 -> begin
(force_uvar t)
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))


let closing_subst = (fun bs -> (let _128_226 = (FStar_List.fold_right (fun _35_475 _35_478 -> (match (((_35_475), (_35_478))) with
| ((x, _35_474), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _128_226 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _35_489 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _128_232 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_489.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_489.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_232}))
in (

let o = (let _128_233 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_128_233)
in (

let _35_495 = (aux bs' o)
in (match (_35_495) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _128_236 = (open_binders' bs)
in (Prims.fst _128_236)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_501 = (open_binders' bs)
in (match (_35_501) with
| (bs', opening) -> begin
(let _128_241 = (subst opening t)
in ((bs'), (_128_241), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_508 = (open_term' bs t)
in (match (_35_508) with
| (b, t, _35_507) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_513 = (open_binders' bs)
in (match (_35_513) with
| (bs', opening) -> begin
(let _128_250 = (subst_comp opening t)
in ((bs'), (_128_250)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_520) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_523) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_529 = p
in (let _128_263 = (let _128_262 = (let _128_261 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_533 -> (match (_35_533) with
| (p, b) -> begin
(let _128_260 = (aux_disj sub renaming p)
in ((_128_260), (b)))
end))))
in ((fv), (_128_261)))
in FStar_Syntax_Syntax.Pat_cons (_128_262))
in {FStar_Syntax_Syntax.v = _128_263; FStar_Syntax_Syntax.ty = _35_529.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_529.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_541 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_544 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _128_265 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_544.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_544.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_265}))
end
| Some (y) -> begin
y
end)
in (

let _35_549 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_549.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_549.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_553 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _128_266 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_553.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_553.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_266}))
in (

let _35_556 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_556.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_556.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_562 = x
in (let _128_267 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_562.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_562.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_267}))
in (

let t0 = (subst sub t0)
in (

let _35_566 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_566.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_566.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_575) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_584 = (aux sub renaming p)
in (match (_35_584) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let _35_586 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_586.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_586.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_606 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_595 _35_598 -> (match (((_35_595), (_35_598))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_602 = (aux sub renaming p)
in (match (_35_602) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (_35_606) with
| (pats, sub, renaming) -> begin
(((

let _35_607 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_607.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_607.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_611 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _128_276 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_611.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_611.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_276}))
in (

let sub = (let _128_277 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_128_277)
in (((

let _35_615 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_615.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_615.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_619 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _128_278 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_619.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_619.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_278}))
in (

let sub = (let _128_279 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_128_279)
in (((

let _35_623 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_623.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_623.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_629 = x
in (let _128_280 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_280}))
in (

let t0 = (subst sub t0)
in (((

let _35_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_633.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let _35_639 = (aux [] [] p)
in (match (_35_639) with
| (p, sub, _35_638) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_643 -> (match (_35_643) with
| (p, wopt, e) -> begin
(

let _35_646 = (open_pat p)
in (match (_35_646) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _128_283 = (subst opening w)
in Some (_128_283))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _128_288 = (closing_subst bs)
in (subst _128_288 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _128_293 = (closing_subst bs)
in (subst_comp _128_293 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _35_666 = x
in (let _128_300 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_666.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_666.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_300}))
in (

let s' = (let _128_301 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_128_301)
in (let _128_302 = (aux s' tl)
in (((x), (imp)))::_128_302)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_673 = lc
in (let _128_309 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_673.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _128_309; FStar_Syntax_Syntax.cflags = _35_673.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_675 -> (match (()) with
| () -> begin
(let _128_308 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _128_308))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_683) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_691 = (aux sub p)
in (match (_35_691) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _128_317 = (aux sub p)
in (Prims.fst _128_317))) ps)
in (((

let _35_694 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_694.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_694.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_711 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_702 _35_705 -> (match (((_35_702), (_35_705))) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_708 = (aux sub p)
in (match (_35_708) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (_35_711) with
| (pats, sub) -> begin
(((

let _35_712 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_712.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_712.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_716 = x
in (let _128_320 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_320}))
in (

let sub = (let _128_321 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_128_321)
in (((

let _35_720 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_720.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_720.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_724 = x
in (let _128_322 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_724.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_724.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_322}))
in (

let sub = (let _128_323 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_128_323)
in (((

let _35_728 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_728.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_728.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_734 = x
in (let _128_324 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_734.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_734.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _128_324}))
in (

let t0 = (subst sub t0)
in (((

let _35_738 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_738.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_738.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_743 -> (match (_35_743) with
| (p, wopt, e) -> begin
(

let _35_746 = (close_pat p)
in (match (_35_746) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _128_327 = (subst closing w)
in Some (_128_327))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let _35_759 = (let _128_332 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _128_332 FStar_List.unzip))
in (match (_35_759) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_764 = (univ_var_opening us)
in (match (_35_764) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_770 = (univ_var_opening us)
in (match (_35_770) with
| (s, us') -> begin
(let _128_341 = (subst_comp s c)
in ((us'), (_128_341)))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _35_796 = (FStar_List.fold_right (fun lb _35_789 -> (match (_35_789) with
| (i, lbs, out) -> begin
(

let x = (let _128_360 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _128_360))
in (((i + (Prims.parse_int "1"))), (((

let _35_791 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_791.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_791.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_791.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_791.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (_35_796) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_808 = (FStar_List.fold_right (fun u _35_802 -> (match (_35_802) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (_35_808) with
| (_35_805, us, u_let_rec_opening) -> begin
(

let _35_809 = lb
in (let _128_364 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_809.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_809.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_809.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _128_364}))
end)))))
in (

let t = (subst let_rec_opening t)
in ((lbs), (t))))
end))
end)


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _35_821 = (FStar_List.fold_right (fun lb _35_818 -> (match (_35_818) with
| (i, out) -> begin
(let _128_374 = (let _128_373 = (let _128_372 = (let _128_371 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_128_371), (i)))
in FStar_Syntax_Syntax.NM (_128_372))
in (_128_373)::out)
in (((i + (Prims.parse_int "1"))), (_128_374)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (_35_821) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_830 = (FStar_List.fold_right (fun u _35_826 -> (match (_35_826) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (_35_830) with
| (_35_828, u_let_rec_closing) -> begin
(

let _35_831 = lb
in (let _128_378 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_831.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_831.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_831.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_831.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _128_378}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_838 -> (match (_35_838) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_845 -> (match (_35_845) with
| (x, _35_844) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_851 -> (match (_35_851) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _128_391 = (subst s t)
in ((us'), (_128_391))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_863 -> (match (_35_863) with
| (x, _35_862) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




