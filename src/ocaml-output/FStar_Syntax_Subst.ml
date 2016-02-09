
open Prims
# 31 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

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

# 40 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(let t' = (let _137_8 = (c ())
in (force_delayed_thunk _137_8))
in (let _35_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_32 -> begin
t
end)
end
| Some (t') -> begin
(let t' = (force_delayed_thunk t')
in (let _35_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_39 -> begin
t
end))

# 51 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

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

# 63 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_to_string = (fun s -> (let _137_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _137_15 (FStar_String.concat ", "))))

# 66 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, t) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some (t)
end
| _35_62 -> begin
None
end))))

# 67 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _137_26 = (FStar_Syntax_Syntax.bv_to_tm (let _35_70 = x
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_137_26))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _35_77 -> begin
None
end))))

# 71 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _35_86 -> begin
None
end))))

# 74 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _35_95 -> begin
None
end))))

# 81 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| s0::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some ((rest, st))
end)
end))

# 88 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let map_some_curry = (fun f x _35_5 -> (match (_35_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 92 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let apply_until_some_then_map = (fun f s g t -> (let _137_64 = (apply_until_some f s)
in (FStar_All.pipe_right _137_64 (map_some_curry g t))))

# 96 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (let u = (compress_univ u)
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
(let _137_69 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_137_69))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _137_70 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_137_70))
end)))

# 112 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_139 -> begin
(let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_158), _35_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _137_86 = (let _137_85 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_137_85))
in (FStar_Syntax_Syntax.mk _137_86 None t0.FStar_Syntax_Syntax.pos))
end
| _35_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _137_91 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_137_91))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_184 -> begin
(let _35_185 = t
in (let _137_98 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _137_97 = (FStar_List.map (fun _35_189 -> (match (_35_189) with
| (t, imp) -> begin
(let _137_95 = (subst' s t)
in (_137_95, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _137_96 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _137_98; FStar_Syntax_Syntax.effect_args = _137_97; FStar_Syntax_Syntax.flags = _137_96}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _137_101 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _137_101))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _137_102 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _137_102))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _137_103 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _137_103))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))

# 167 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

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
| FStar_Syntax_Syntax.NT (_35_224) -> begin
s
end))

# 173 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun n s -> (FStar_List.map (shift n) s))

# 174 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 175 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_binder' = (fun s _35_233 -> (match (_35_233) with
| (x, imp) -> begin
(let _137_121 = (let _35_234 = x
in (let _137_120 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_120}))
in (_137_121, imp))
end))

# 176 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _137_126 = (shift_subst' i s)
in (subst_binder' _137_126 b))
end))))

# 180 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_arg' = (fun s _35_243 -> (match (_35_243) with
| (t, imp) -> begin
(let _137_129 = (subst' s t)
in (_137_129, imp))
end))

# 181 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

# 182 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_pat' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _35_261 = (aux n p)
in (match (_35_261) with
| (p, m) -> begin
(let ps = (FStar_List.map (fun p -> (let _137_142 = (aux n p)
in (Prims.fst _137_142))) ps)
in ((let _35_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _35_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_272 _35_275 -> (match ((_35_272, _35_275)) with
| ((pats, n), (p, imp)) -> begin
(let _35_278 = (aux n p)
in (match (_35_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_281) with
| (pats, n) -> begin
((let _35_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _35_287 = x
in (let _137_145 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_145}))
in ((let _35_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _35_295 = x
in (let _137_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_146}))
in ((let _35_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let s = (shift_subst' n s)
in (let x = (let _35_305 = x
in (let _137_147 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_147}))
in (let t0 = (subst' s t0)
in ((let _35_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 216 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _137_155 = (let _35_316 = l
in (let _137_154 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _137_154; FStar_Syntax_Syntax.cflags = _35_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_318 -> (match (()) with
| () -> begin
(let _137_153 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _137_153))
end))}))
in Some (_137_155))
end))

# 222 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_322) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _137_166 = (let _137_165 = (let _137_164 = (subst' s t0)
in (let _137_163 = (subst_args' s args)
in (_137_164, _137_163)))
in FStar_Syntax_Syntax.Tm_app (_137_165))
in (FStar_Syntax_Syntax.mk _137_166 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _137_170 = (let _137_169 = (let _137_168 = (subst' s t0)
in (let _137_167 = (subst' s t1)
in (_137_168, _137_167, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_137_169))
in (FStar_Syntax_Syntax.mk _137_170 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let n = (FStar_List.length bs)
in (let s' = (shift_subst' n s)
in (let _137_175 = (let _137_174 = (let _137_173 = (subst_binders' s bs)
in (let _137_172 = (subst' s' body)
in (let _137_171 = (push_subst_lcomp s' lopt)
in (_137_173, _137_172, _137_171))))
in FStar_Syntax_Syntax.Tm_abs (_137_174))
in (FStar_Syntax_Syntax.mk _137_175 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(let n = (FStar_List.length bs)
in (let _137_180 = (let _137_179 = (let _137_178 = (subst_binders' s bs)
in (let _137_177 = (let _137_176 = (shift_subst' n s)
in (subst_comp' _137_176 comp))
in (_137_178, _137_177)))
in FStar_Syntax_Syntax.Tm_arrow (_137_179))
in (FStar_Syntax_Syntax.mk _137_180 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let x = (let _35_373 = x
in (let _137_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_181}))
in (let phi = (let _137_182 = (shift_subst' 1 s)
in (subst' _137_182 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(let t0 = (subst' s t0)
in (let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_385 -> (match (_35_385) with
| (pat, wopt, branch) -> begin
(let _35_388 = (subst_pat' s pat)
in (match (_35_388) with
| (pat, n) -> begin
(let s = (shift_subst' n s)
in (let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_184 = (subst' s w)
in Some (_137_184))
end)
in (let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(let n = (FStar_List.length lbs)
in (let sn = (shift_subst' n s)
in (let body = (subst' sn body)
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (let _35_408 = lb
in {FStar_Syntax_Syntax.lbname = _35_408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _137_190 = (let _137_189 = (let _137_188 = (subst' s t0)
in (let _137_187 = (let _137_186 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_137_186))
in (_137_188, _137_187)))
in FStar_Syntax_Syntax.Tm_meta (_137_189))
in (FStar_Syntax_Syntax.mk _137_190 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _137_193 = (let _137_192 = (let _137_191 = (subst' s t)
in (_137_191, m))
in FStar_Syntax_Syntax.Tm_meta (_137_192))
in (FStar_Syntax_Syntax.mk _137_193 None t.FStar_Syntax_Syntax.pos))
end))

# 289 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let rec compress : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(let t' = (let _137_196 = (push_subst s t)
in (compress _137_196))
in (let _35_430 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_433 -> begin
(force_uvar t)
end)))

# 300 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (subst' ((s)::[]) t))

# 301 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (subst_comp' ((s)::[]) t))

# 302 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let closing_subst = (fun bs -> (let _137_208 = (FStar_List.fold_right (fun _35_442 _35_445 -> (match ((_35_442, _35_445)) with
| ((x, _35_441), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _137_208 Prims.fst)))

# 304 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_binders' = (fun bs -> (let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(let x' = (let _35_456 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _137_214 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_214}))
in (let o = (let _137_218 = (let _137_216 = (let _137_215 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _137_215))
in FStar_Syntax_Syntax.DB (_137_216))
in (let _137_217 = (shift_subst 1 o)
in (_137_218)::_137_217))
in (let _35_462 = (aux bs' o)
in (match (_35_462) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 313 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun bs -> (let _137_221 = (open_binders' bs)
in (Prims.fst _137_221)))

# 314 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_term' : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun bs t -> (let _35_468 = (open_binders' bs)
in (match (_35_468) with
| (bs', opening) -> begin
(let _137_226 = (subst opening t)
in (bs', _137_226, opening))
end)))

# 317 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_term : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun bs t -> (let _35_475 = (open_term' bs t)
in (match (_35_475) with
| (b, t, _35_474) -> begin
(b, t)
end)))

# 320 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_comp : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax) = (fun bs t -> (let _35_480 = (open_binders' bs)
in (match (_35_480) with
| (bs', opening) -> begin
(let _137_235 = (subst_comp opening t)
in (bs', _137_235))
end)))

# 323 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_pat : FStar_Syntax_Syntax.pat  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_488) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _35_496 = (aux sub p)
in (match (_35_496) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _137_243 = (aux sub p)
in (Prims.fst _137_243))) ps)
in ((let _35_499 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_499.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_499.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _35_516 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_507 _35_510 -> (match ((_35_507, _35_510)) with
| ((pats, sub), (p, imp)) -> begin
(let _35_513 = (aux sub p)
in (match (_35_513) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_516) with
| (pats, sub) -> begin
((let _35_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_517.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_517.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x' = (let _35_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _137_246 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_246}))
in (let sub = (let _137_250 = (let _137_248 = (let _137_247 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _137_247))
in FStar_Syntax_Syntax.DB (_137_248))
in (let _137_249 = (shift_subst 1 sub)
in (_137_250)::_137_249))
in ((let _35_525 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_525.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_525.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x' = (let _35_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _137_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_251}))
in (let sub = (let _137_255 = (let _137_253 = (let _137_252 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _137_252))
in FStar_Syntax_Syntax.DB (_137_253))
in (let _137_254 = (shift_subst 1 sub)
in (_137_255)::_137_254))
in ((let _35_533 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_533.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _35_539 = x
in (let _137_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_256}))
in (let t0 = (subst sub t0)
in ((let _35_543 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_543.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_543.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 357 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_branch : (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun _35_548 -> (match (_35_548) with
| (p, wopt, e) -> begin
(let _35_551 = (open_pat p)
in (match (_35_551) with
| (p, opening) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_259 = (subst opening w)
in Some (_137_259))
end)
in (let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 365 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs t -> (let _137_264 = (closing_subst bs)
in (subst _137_264 t)))

# 366 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun bs c -> (let _137_269 = (closing_subst bs)
in (subst_comp _137_269 c)))

# 367 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun bs -> (let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(let x = (let _35_571 = x
in (let _137_276 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_276}))
in (let s' = (let _137_277 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_137_277)
in (let _137_278 = (aux s' tl)
in ((x, imp))::_137_278)))
end))
in (aux [] bs)))

# 376 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (let s = (closing_subst bs)
in (let _35_578 = lc
in (let _137_285 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_578.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _137_285; FStar_Syntax_Syntax.cflags = _35_578.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_580 -> (match (()) with
| () -> begin
(let _137_284 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _137_284))
end))}))))

# 381 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_588) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _35_596 = (aux sub p)
in (match (_35_596) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _137_293 = (aux sub p)
in (Prims.fst _137_293))) ps)
in ((let _35_599 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_599.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_599.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _35_616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_607 _35_610 -> (match ((_35_607, _35_610)) with
| ((pats, sub), (p, imp)) -> begin
(let _35_613 = (aux sub p)
in (match (_35_613) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_616) with
| (pats, sub) -> begin
((let _35_617 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_617.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_617.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x = (let _35_621 = x
in (let _137_296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_296}))
in (let sub = (let _137_297 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_137_297)
in ((let _35_625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_625.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_625.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x = (let _35_629 = x
in (let _137_298 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_298}))
in (let sub = (let _137_299 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_137_299)
in ((let _35_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_633.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _35_639 = x
in (let _137_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_300}))
in (let t0 = (subst sub t0)
in ((let _35_643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_643.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_643.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 414 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_branch : ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun _35_648 -> (match (_35_648) with
| (p, wopt, e) -> begin
(let _35_651 = (close_pat p)
in (match (_35_651) with
| (p, closing) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_303 = (subst closing w)
in Some (_137_303))
end)
in (let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 422 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Ident.ident Prims.list) = (fun us -> (let n = ((FStar_List.length us) - 1)
in (let _35_664 = (let _137_308 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _137_308 FStar_List.unzip))
in (match (_35_664) with
| (s, us') -> begin
(s, us')
end))))

# 429 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (let _35_669 = (univ_var_opening us)
in (match (_35_669) with
| (s, us') -> begin
(let t = (subst s t)
in (us', t))
end)))

# 434 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (let _35_675 = (univ_var_opening us)
in (match (_35_675) with
| (s, us') -> begin
(let _137_317 = (subst_comp s c)
in (us', _137_317))
end)))

# 438 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun us t -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 443 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun us c -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 448 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let is_top_level : FStar_Syntax_Syntax.letbinding Prims.list  ->  Prims.bool = (fun _35_7 -> (match (_35_7) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_35_700); FStar_Syntax_Syntax.lbunivs = _35_698; FStar_Syntax_Syntax.lbtyp = _35_696; FStar_Syntax_Syntax.lbeff = _35_694; FStar_Syntax_Syntax.lbdef = _35_692}::_35_690 -> begin
true
end
| _35_705 -> begin
false
end))

# 452 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: open_let_rec")
end)

# 456 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: close_let_rec")
end)

# 461 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let mk_subst_binders = (fun args -> (let _35_718 = (FStar_List.fold_right (fun a _35_714 -> (match (_35_714) with
| (s, i) -> begin
((FStar_Syntax_Syntax.DB ((i, (Prims.fst a))))::s, (i + 1))
end)) args ([], 0))
in (match (_35_718) with
| (s, _35_717) -> begin
s
end)))

# 465 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs args t -> (let _137_349 = (mk_subst_binders args)
in (subst _137_349 t)))

# 466 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let subst_binders_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun bs args t -> (let _137_356 = (mk_subst_binders args)
in (subst_comp _137_356 t)))

# 469 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Ident.ident Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun binders _35_728 -> (match (_35_728) with
| (us, t) -> begin
(let n = ((FStar_List.length binders) - 1)
in (let k = (FStar_List.length us)
in (let s = (FStar_List.mapi (fun i _35_735 -> (match (_35_735) with
| (x, _35_734) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (let t = (subst s t)
in (us, t)))))
end))

# 476 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Ident.ident Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun us _35_741 -> (match (_35_741) with
| (us', t) -> begin
(let n = ((FStar_List.length us) - 1)
in (let k = (FStar_List.length us')
in (let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _137_369 = (subst s t)
in (us', _137_369)))))
end))

# 482 "D:\\workspace\\universes\\FStar\\src\\syntax\\subst.fs"

let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun bs -> (let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_753 -> (match (_35_753) with
| (x, _35_752) -> begin
(let _137_375 = (let _137_374 = (FStar_Syntax_Syntax.bv_to_name x)
in ((n - i), _137_374))
in FStar_Syntax_Syntax.DB (_137_375))
end))))))




