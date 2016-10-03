
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

let t' = (let _132_8 = (c ())
in (force_delayed_thunk _132_8))
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


let subst_to_string = (fun s -> (let _132_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _132_15 (FStar_String.concat ", "))))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _132_23 = (let _132_22 = (let _132_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _132_21))
in (FStar_Syntax_Syntax.bv_to_name _132_22))
in Some (_132_23))
end
| _35_62 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _132_29 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_70 = a
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_132_29))
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


let apply_until_some_then_map = (fun f s g t -> (let _132_67 = (apply_until_some f s)
in (FStar_All.pipe_right _132_67 (map_some_curry g t))))


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
(let _132_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_132_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _132_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_132_73))
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
(let _132_89 = (let _132_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_132_88))
in (FStar_Syntax_Syntax.mk _132_89 None t0.FStar_Syntax_Syntax.pos))
end
| _35_172 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _132_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_132_94))
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
in (let _132_102 = (FStar_List.map (subst_univ s) t.FStar_Syntax_Syntax.comp_univs)
in (let _132_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _132_100 = (FStar_List.map (fun _35_190 -> (match (_35_190) with
| (t, imp) -> begin
(let _132_98 = (subst' s t)
in ((_132_98), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _132_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = _132_102; FStar_Syntax_Syntax.effect_name = _35_186.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _132_101; FStar_Syntax_Syntax.effect_args = _132_100; FStar_Syntax_Syntax.flags = _132_99})))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _35_197 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _132_106 = (subst' s t)
in (let _132_105 = (FStar_Option.map (subst_univ s) uopt)
in (FStar_Syntax_Syntax.mk_Total' _132_106 _132_105)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _132_108 = (subst' s t)
in (let _132_107 = (FStar_Option.map (subst_univ s) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _132_108 _132_107)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _132_109 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _132_109))
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
| FStar_Syntax_Syntax.NT (_35_229) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))


let subst_binder' = (fun s _35_238 -> (match (_35_238) with
| (x, imp) -> begin
(let _132_127 = (

let _35_239 = x
in (let _132_126 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_239.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_239.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_126}))
in ((_132_127), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = (Prims.parse_int "0")) then begin
(subst_binder' s b)
end else begin
(let _132_132 = (shift_subst' i s)
in (subst_binder' _132_132 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' ((s)::[]) bs))


let subst_arg' = (fun s _35_250 -> (match (_35_250) with
| (t, imp) -> begin
(let _132_139 = (subst' s t)
in ((_132_139), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_260) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_268 = (aux n p)
in (match (_35_268) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _132_152 = (aux n p)
in (Prims.fst _132_152))) ps)
in (((

let _35_271 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_271.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_271.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_288 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_279 _35_282 -> (match (((_35_279), (_35_282))) with
| ((pats, n), (p, imp)) -> begin
(

let _35_285 = (aux n p)
in (match (_35_285) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (_35_288) with
| (pats, n) -> begin
(((

let _35_289 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_289.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_289.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_294 = x
in (let _132_155 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_155}))
in (((

let _35_297 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_297.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_297.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_302 = x
in (let _132_156 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_302.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_302.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_156}))
in (((

let _35_305 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_305.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_305.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_312 = x
in (let _132_157 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_157}))
in (

let t0 = (subst' s t0)
in (((

let _35_316 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_316.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_316.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _132_164 = (let _132_163 = (

let _35_328 = l
in (let _132_162 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_328.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _132_162; FStar_Syntax_Syntax.cflags = _35_328.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_330 -> (match (()) with
| () -> begin
(let _132_161 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _132_161))
end))}))
in FStar_Util.Inl (_132_163))
in Some (_132_164))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_334) -> begin
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
(let _132_175 = (let _132_174 = (let _132_173 = (subst' s t0)
in (let _132_172 = (subst_args' s args)
in ((_132_173), (_132_172))))
in FStar_Syntax_Syntax.Tm_app (_132_174))
in (FStar_Syntax_Syntax.mk _132_175 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _132_180 = (let _132_179 = (let _132_178 = (subst' s t0)
in (let _132_177 = (let _132_176 = (subst' s t1)
in FStar_Util.Inl (_132_176))
in ((_132_178), (_132_177), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_132_179))
in (FStar_Syntax_Syntax.mk _132_180 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _132_185 = (let _132_184 = (let _132_183 = (subst' s t0)
in (let _132_182 = (let _132_181 = (subst_comp' s c)
in FStar_Util.Inr (_132_181))
in ((_132_183), (_132_182), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_132_184))
in (FStar_Syntax_Syntax.mk _132_185 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _132_190 = (let _132_189 = (let _132_188 = (subst_binders' s bs)
in (let _132_187 = (subst' s' body)
in (let _132_186 = (push_subst_lcomp s' lopt)
in ((_132_188), (_132_187), (_132_186)))))
in FStar_Syntax_Syntax.Tm_abs (_132_189))
in (FStar_Syntax_Syntax.mk _132_190 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _132_195 = (let _132_194 = (let _132_193 = (subst_binders' s bs)
in (let _132_192 = (let _132_191 = (shift_subst' n s)
in (subst_comp' _132_191 comp))
in ((_132_193), (_132_192))))
in FStar_Syntax_Syntax.Tm_arrow (_132_194))
in (FStar_Syntax_Syntax.mk _132_195 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_392 = x
in (let _132_196 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_196}))
in (

let phi = (let _132_197 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _132_197 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_404 -> (match (_35_404) with
| (pat, wopt, branch) -> begin
(

let _35_407 = (subst_pat' s pat)
in (match (_35_407) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _132_199 = (subst' s w)
in Some (_132_199))
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

let _35_429 = x
in {FStar_Syntax_Syntax.ppname = _35_429.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_429.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _35_433 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _35_435 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_435.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_435.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_433.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_433.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _35_438 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_438.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_438.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _132_205 = (let _132_204 = (let _132_203 = (subst' s t0)
in (let _132_202 = (let _132_201 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_132_201))
in ((_132_203), (_132_202))))
in FStar_Syntax_Syntax.Tm_meta (_132_204))
in (FStar_Syntax_Syntax.mk _132_205 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(let _132_211 = (let _132_210 = (let _132_209 = (subst' s t0)
in (let _132_208 = (let _132_207 = (let _132_206 = (subst' s t)
in ((m), (_132_206)))
in FStar_Syntax_Syntax.Meta_monadic (_132_207))
in ((_132_209), (_132_208))))
in FStar_Syntax_Syntax.Tm_meta (_132_210))
in (FStar_Syntax_Syntax.mk _132_211 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _132_214 = (let _132_213 = (let _132_212 = (subst' s t)
in ((_132_212), (m)))
in FStar_Syntax_Syntax.Tm_meta (_132_213))
in (FStar_Syntax_Syntax.mk _132_214 None t.FStar_Syntax_Syntax.pos))
end))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _132_217 = (push_subst s t)
in (compress _132_217))
in (

let _35_467 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_470 -> begin
(force_uvar t)
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))


let closing_subst = (fun bs -> (let _132_229 = (FStar_List.fold_right (fun _35_479 _35_482 -> (match (((_35_479), (_35_482))) with
| ((x, _35_478), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _132_229 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _35_493 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _132_235 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_493.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_493.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_235}))
in (

let o = (let _132_236 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_132_236)
in (

let _35_499 = (aux bs' o)
in (match (_35_499) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _132_239 = (open_binders' bs)
in (Prims.fst _132_239)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_505 = (open_binders' bs)
in (match (_35_505) with
| (bs', opening) -> begin
(let _132_244 = (subst opening t)
in ((bs'), (_132_244), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_512 = (open_term' bs t)
in (match (_35_512) with
| (b, t, _35_511) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_517 = (open_binders' bs)
in (match (_35_517) with
| (bs', opening) -> begin
(let _132_253 = (subst_comp opening t)
in ((bs'), (_132_253)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_524) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_527) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_533 = p
in (let _132_266 = (let _132_265 = (let _132_264 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_537 -> (match (_35_537) with
| (p, b) -> begin
(let _132_263 = (aux_disj sub renaming p)
in ((_132_263), (b)))
end))))
in ((fv), (_132_264)))
in FStar_Syntax_Syntax.Pat_cons (_132_265))
in {FStar_Syntax_Syntax.v = _132_266; FStar_Syntax_Syntax.ty = _35_533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_533.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_545 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_548 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _132_268 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_548.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_548.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_268}))
end
| Some (y) -> begin
y
end)
in (

let _35_553 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_553.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_553.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_557 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _132_269 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_557.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_557.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_269}))
in (

let _35_560 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_560.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_560.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_566 = x
in (let _132_270 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_270}))
in (

let t0 = (subst sub t0)
in (

let _35_570 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_570.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_570.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_579) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_588 = (aux sub renaming p)
in (match (_35_588) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let _35_590 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_590.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_590.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_610 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_599 _35_602 -> (match (((_35_599), (_35_602))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_606 = (aux sub renaming p)
in (match (_35_606) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (_35_610) with
| (pats, sub, renaming) -> begin
(((

let _35_611 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_611.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_611.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_615 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _132_279 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_615.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_615.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_279}))
in (

let sub = (let _132_280 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_132_280)
in (((

let _35_619 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_619.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_619.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_623 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _132_281 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_623.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_623.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_281}))
in (

let sub = (let _132_282 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_132_282)
in (((

let _35_627 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_627.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_627.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_633 = x
in (let _132_283 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_633.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_633.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_283}))
in (

let t0 = (subst sub t0)
in (((

let _35_637 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_637.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_637.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let _35_643 = (aux [] [] p)
in (match (_35_643) with
| (p, sub, _35_642) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_647 -> (match (_35_647) with
| (p, wopt, e) -> begin
(

let _35_650 = (open_pat p)
in (match (_35_650) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _132_286 = (subst opening w)
in Some (_132_286))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _132_291 = (closing_subst bs)
in (subst _132_291 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _132_296 = (closing_subst bs)
in (subst_comp _132_296 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _35_670 = x
in (let _132_303 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_670.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_670.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_303}))
in (

let s' = (let _132_304 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_132_304)
in (let _132_305 = (aux s' tl)
in (((x), (imp)))::_132_305)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_677 = lc
in (let _132_312 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_677.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _132_312; FStar_Syntax_Syntax.cflags = _35_677.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_679 -> (match (()) with
| () -> begin
(let _132_311 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _132_311))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_687) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_695 = (aux sub p)
in (match (_35_695) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _132_320 = (aux sub p)
in (Prims.fst _132_320))) ps)
in (((

let _35_698 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_698.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_698.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_715 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_706 _35_709 -> (match (((_35_706), (_35_709))) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_712 = (aux sub p)
in (match (_35_712) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (_35_715) with
| (pats, sub) -> begin
(((

let _35_716 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_716.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_716.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_720 = x
in (let _132_323 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_720.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_720.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_323}))
in (

let sub = (let _132_324 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_132_324)
in (((

let _35_724 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_724.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_724.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_728 = x
in (let _132_325 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_728.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_728.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_325}))
in (

let sub = (let _132_326 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_132_326)
in (((

let _35_732 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_732.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_732.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_738 = x
in (let _132_327 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_738.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_738.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_327}))
in (

let t0 = (subst sub t0)
in (((

let _35_742 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_742.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_742.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_747 -> (match (_35_747) with
| (p, wopt, e) -> begin
(

let _35_750 = (close_pat p)
in (match (_35_750) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _132_330 = (subst closing w)
in Some (_132_330))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let _35_763 = (let _132_335 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _132_335 FStar_List.unzip))
in (match (_35_763) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_768 = (univ_var_opening us)
in (match (_35_768) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_774 = (univ_var_opening us)
in (match (_35_774) with
| (s, us') -> begin
(let _132_344 = (subst_comp s c)
in ((us'), (_132_344)))
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

let _35_800 = (FStar_List.fold_right (fun lb _35_793 -> (match (_35_793) with
| (i, lbs, out) -> begin
(

let x = (let _132_363 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _132_363))
in (((i + (Prims.parse_int "1"))), (((

let _35_795 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_795.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_795.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_795.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_795.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (_35_800) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_812 = (FStar_List.fold_right (fun u _35_806 -> (match (_35_806) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (_35_812) with
| (_35_809, us, u_let_rec_opening) -> begin
(

let _35_813 = lb
in (let _132_367 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_813.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_813.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_813.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _132_367}))
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

let _35_825 = (FStar_List.fold_right (fun lb _35_822 -> (match (_35_822) with
| (i, out) -> begin
(let _132_377 = (let _132_376 = (let _132_375 = (let _132_374 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_132_374), (i)))
in FStar_Syntax_Syntax.NM (_132_375))
in (_132_376)::out)
in (((i + (Prims.parse_int "1"))), (_132_377)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (_35_825) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_834 = (FStar_List.fold_right (fun u _35_830 -> (match (_35_830) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (_35_834) with
| (_35_832, u_let_rec_closing) -> begin
(

let _35_835 = lb
in (let _132_381 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_835.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_835.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_835.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_835.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _132_381}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_842 -> (match (_35_842) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_849 -> (match (_35_849) with
| (x, _35_848) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_855 -> (match (_35_855) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _132_394 = (subst s t)
in ((us'), (_132_394))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_867 -> (match (_35_867) with
| (x, _35_866) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




