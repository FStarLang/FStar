
open Prims
# 56 "FStar.Syntax.Subst.fst"
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

# 65 "FStar.Syntax.Subst.fst"
let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(
# 70 "FStar.Syntax.Subst.fst"
let t' = (let _124_8 = (c ())
in (force_delayed_thunk _124_8))
in (
# 70 "FStar.Syntax.Subst.fst"
let _35_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 73 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 73 "FStar.Syntax.Subst.fst"
let _35_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_39 -> begin
t
end))

# 76 "FStar.Syntax.Subst.fst"
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

# 88 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _124_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _124_15 (FStar_String.concat ", "))))

# 91 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _124_23 = (let _124_22 = (let _124_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _124_21))
in (FStar_Syntax_Syntax.bv_to_name _124_22))
in Some (_124_23))
end
| _35_62 -> begin
None
end))))

# 95 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_29 = (FStar_Syntax_Syntax.bv_to_tm (
# 96 "FStar.Syntax.Subst.fst"
let _35_70 = a
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_124_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _35_77 -> begin
None
end))))

# 99 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _35_86 -> begin
None
end))))

# 102 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _35_95 -> begin
None
end))))

# 109 "FStar.Syntax.Subst.fst"
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

# 116 "FStar.Syntax.Subst.fst"
let map_some_curry = (fun f x _35_5 -> (match (_35_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 120 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _124_67 = (apply_until_some f s)
in (FStar_All.pipe_right _124_67 (map_some_curry g t))))

# 124 "FStar.Syntax.Subst.fst"
let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (
# 125 "FStar.Syntax.Subst.fst"
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
(let _124_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_124_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _124_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_124_73))
end)))

# 140 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_139 -> begin
(
# 144 "FStar.Syntax.Subst.fst"
let t0 = (force_delayed_thunk t)
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
(let _124_89 = (let _124_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_124_88))
in (FStar_Syntax_Syntax.mk _124_89 None t0.FStar_Syntax_Syntax.pos))
end
| _35_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _124_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_124_94))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_184 -> begin
(
# 180 "FStar.Syntax.Subst.fst"
let _35_185 = t
in (let _124_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _124_100 = (FStar_List.map (fun _35_189 -> (match (_35_189) with
| (t, imp) -> begin
(let _124_98 = (subst' s t)
in (_124_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _124_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _124_101; FStar_Syntax_Syntax.effect_args = _124_100; FStar_Syntax_Syntax.flags = _124_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _124_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _124_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _124_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _124_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _124_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _124_106))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))

# 195 "FStar.Syntax.Subst.fst"
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

# 201 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 202 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 203 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _35_233 -> (match (_35_233) with
| (x, imp) -> begin
(let _124_124 = (
# 203 "FStar.Syntax.Subst.fst"
let _35_234 = x
in (let _124_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_123}))
in (_124_124, imp))
end))

# 204 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _124_129 = (shift_subst' i s)
in (subst_binder' _124_129 b))
end))))

# 208 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _35_243 -> (match (_35_243) with
| (t, imp) -> begin
(let _124_132 = (subst' s t)
in (_124_132, imp))
end))

# 209 "FStar.Syntax.Subst.fst"
let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

# 210 "FStar.Syntax.Subst.fst"
let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (
# 211 "FStar.Syntax.Subst.fst"
let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let _35_261 = (aux n p)
in (match (_35_261) with
| (p, m) -> begin
(
# 218 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _124_145 = (aux n p)
in (Prims.fst _124_145))) ps)
in ((
# 219 "FStar.Syntax.Subst.fst"
let _35_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _35_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_272 _35_275 -> (match ((_35_272, _35_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 223 "FStar.Syntax.Subst.fst"
let _35_278 = (aux n p)
in (match (_35_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_281) with
| (pats, n) -> begin
((
# 225 "FStar.Syntax.Subst.fst"
let _35_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 228 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 229 "FStar.Syntax.Subst.fst"
let x = (
# 229 "FStar.Syntax.Subst.fst"
let _35_287 = x
in (let _124_148 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_148}))
in ((
# 230 "FStar.Syntax.Subst.fst"
let _35_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 233 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 234 "FStar.Syntax.Subst.fst"
let x = (
# 234 "FStar.Syntax.Subst.fst"
let _35_295 = x
in (let _124_149 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_149}))
in ((
# 235 "FStar.Syntax.Subst.fst"
let _35_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 238 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 239 "FStar.Syntax.Subst.fst"
let x = (
# 239 "FStar.Syntax.Subst.fst"
let _35_305 = x
in (let _124_150 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_150}))
in (
# 240 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 241 "FStar.Syntax.Subst.fst"
let _35_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 244 "FStar.Syntax.Subst.fst"
let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _124_157 = (let _124_156 = (
# 248 "FStar.Syntax.Subst.fst"
let _35_321 = l
in (let _124_155 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_321.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_155; FStar_Syntax_Syntax.cflags = _35_321.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_323 -> (match (()) with
| () -> begin
(let _124_154 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _124_154))
end))}))
in FStar_Util.Inl (_124_156))
in Some (_124_157))
end))

# 251 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_327) -> begin
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
# 267 "FStar.Syntax.Subst.fst"
let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _124_168 = (let _124_167 = (let _124_166 = (subst' s t0)
in (let _124_165 = (subst_args' s args)
in (_124_166, _124_165)))
in FStar_Syntax_Syntax.Tm_app (_124_167))
in (FStar_Syntax_Syntax.mk _124_168 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _124_173 = (let _124_172 = (let _124_171 = (subst' s t0)
in (let _124_170 = (let _124_169 = (subst' s t1)
in FStar_Util.Inl (_124_169))
in (_124_171, _124_170, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_172))
in (FStar_Syntax_Syntax.mk _124_173 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _124_178 = (let _124_177 = (let _124_176 = (subst' s t0)
in (let _124_175 = (let _124_174 = (subst_comp' s c)
in FStar_Util.Inr (_124_174))
in (_124_176, _124_175, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_177))
in (FStar_Syntax_Syntax.mk _124_178 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 276 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 277 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _124_183 = (let _124_182 = (let _124_181 = (subst_binders' s bs)
in (let _124_180 = (subst' s' body)
in (let _124_179 = (push_subst_lcomp s' lopt)
in (_124_181, _124_180, _124_179))))
in FStar_Syntax_Syntax.Tm_abs (_124_182))
in (FStar_Syntax_Syntax.mk _124_183 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 281 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _124_188 = (let _124_187 = (let _124_186 = (subst_binders' s bs)
in (let _124_185 = (let _124_184 = (shift_subst' n s)
in (subst_comp' _124_184 comp))
in (_124_186, _124_185)))
in FStar_Syntax_Syntax.Tm_arrow (_124_187))
in (FStar_Syntax_Syntax.mk _124_188 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 285 "FStar.Syntax.Subst.fst"
let x = (
# 285 "FStar.Syntax.Subst.fst"
let _35_385 = x
in (let _124_189 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_385.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_385.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_189}))
in (
# 286 "FStar.Syntax.Subst.fst"
let phi = (let _124_190 = (shift_subst' 1 s)
in (subst' _124_190 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 290 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 291 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_397 -> (match (_35_397) with
| (pat, wopt, branch) -> begin
(
# 292 "FStar.Syntax.Subst.fst"
let _35_400 = (subst_pat' s pat)
in (match (_35_400) with
| (pat, n) -> begin
(
# 293 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 294 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_192 = (subst' s w)
in Some (_124_192))
end)
in (
# 297 "FStar.Syntax.Subst.fst"
let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(
# 302 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length lbs)
in (
# 303 "FStar.Syntax.Subst.fst"
let sn = (shift_subst' n s)
in (
# 304 "FStar.Syntax.Subst.fst"
let body = (subst' sn body)
in (
# 305 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 306 "FStar.Syntax.Subst.fst"
let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (
# 307 "FStar.Syntax.Subst.fst"
let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (
# 310 "FStar.Syntax.Subst.fst"
let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((
# 311 "FStar.Syntax.Subst.fst"
let _35_422 = x
in {FStar_Syntax_Syntax.ppname = _35_422.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_422.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((
# 312 "FStar.Syntax.Subst.fst"
let _35_426 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 312 "FStar.Syntax.Subst.fst"
let _35_428 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_428.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_428.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_426.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_426.FStar_Syntax_Syntax.fv_qual}))
end)
in (
# 313 "FStar.Syntax.Subst.fst"
let _35_431 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_431.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_431.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _124_198 = (let _124_197 = (let _124_196 = (subst' s t0)
in (let _124_195 = (let _124_194 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_124_194))
in (_124_196, _124_195)))
in FStar_Syntax_Syntax.Tm_meta (_124_197))
in (FStar_Syntax_Syntax.mk _124_198 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _124_201 = (let _124_200 = (let _124_199 = (subst' s t)
in (_124_199, m))
in FStar_Syntax_Syntax.Tm_meta (_124_200))
in (FStar_Syntax_Syntax.mk _124_201 None t.FStar_Syntax_Syntax.pos))
end))

# 322 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 323 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 326 "FStar.Syntax.Subst.fst"
let t' = (let _124_204 = (push_subst s t)
in (compress _124_204))
in (
# 327 "FStar.Syntax.Subst.fst"
let _35_453 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_456 -> begin
(force_uvar t)
end)))

# 333 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 334 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 335 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _124_216 = (FStar_List.fold_right (fun _35_465 _35_468 -> (match ((_35_465, _35_468)) with
| ((x, _35_464), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _124_216 Prims.fst)))

# 337 "FStar.Syntax.Subst.fst"
let open_binders' = (fun bs -> (
# 338 "FStar.Syntax.Subst.fst"
let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(
# 341 "FStar.Syntax.Subst.fst"
let x' = (
# 341 "FStar.Syntax.Subst.fst"
let _35_479 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_222 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_479.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_479.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_222}))
in (
# 342 "FStar.Syntax.Subst.fst"
let o = (let _124_223 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_223)
in (
# 343 "FStar.Syntax.Subst.fst"
let _35_485 = (aux bs' o)
in (match (_35_485) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 346 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _124_226 = (open_binders' bs)
in (Prims.fst _124_226)))

# 347 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 348 "FStar.Syntax.Subst.fst"
let _35_491 = (open_binders' bs)
in (match (_35_491) with
| (bs', opening) -> begin
(let _124_231 = (subst opening t)
in (bs', _124_231, opening))
end)))

# 350 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 351 "FStar.Syntax.Subst.fst"
let _35_498 = (open_term' bs t)
in (match (_35_498) with
| (b, t, _35_497) -> begin
(b, t)
end)))

# 353 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 354 "FStar.Syntax.Subst.fst"
let _35_503 = (open_binders' bs)
in (match (_35_503) with
| (bs', opening) -> begin
(let _124_240 = (subst_comp opening t)
in (bs', _124_240))
end)))

# 358 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (
# 359 "FStar.Syntax.Subst.fst"
let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_510) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_513) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 366 "FStar.Syntax.Subst.fst"
let _35_519 = p
in (let _124_253 = (let _124_252 = (let _124_251 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_523 -> (match (_35_523) with
| (p, b) -> begin
(let _124_250 = (aux_disj sub renaming p)
in (_124_250, b))
end))))
in (fv, _124_251))
in FStar_Syntax_Syntax.Pat_cons (_124_252))
in {FStar_Syntax_Syntax.v = _124_253; FStar_Syntax_Syntax.ty = _35_519.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_519.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 370 "FStar.Syntax.Subst.fst"
let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_531 -> begin
None
end)))
in (
# 373 "FStar.Syntax.Subst.fst"
let y = (match (yopt) with
| None -> begin
(
# 374 "FStar.Syntax.Subst.fst"
let _35_534 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_255 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_534.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_534.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_255}))
end
| Some (y) -> begin
y
end)
in (
# 376 "FStar.Syntax.Subst.fst"
let _35_539 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_539.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_539.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 379 "FStar.Syntax.Subst.fst"
let x' = (
# 379 "FStar.Syntax.Subst.fst"
let _35_543 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_256}))
in (
# 380 "FStar.Syntax.Subst.fst"
let _35_546 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_546.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_546.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 383 "FStar.Syntax.Subst.fst"
let x = (
# 383 "FStar.Syntax.Subst.fst"
let _35_552 = x
in (let _124_257 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_552.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_552.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_257}))
in (
# 384 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in (
# 385 "FStar.Syntax.Subst.fst"
let _35_556 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_556.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_556.FStar_Syntax_Syntax.p})))
end))
in (
# 387 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_565) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 393 "FStar.Syntax.Subst.fst"
let _35_574 = (aux sub renaming p)
in (match (_35_574) with
| (p, sub, renaming) -> begin
(
# 394 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((
# 395 "FStar.Syntax.Subst.fst"
let _35_576 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_576.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_576.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 398 "FStar.Syntax.Subst.fst"
let _35_596 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_585 _35_588 -> (match ((_35_585, _35_588)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(
# 399 "FStar.Syntax.Subst.fst"
let _35_592 = (aux sub renaming p)
in (match (_35_592) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_35_596) with
| (pats, sub, renaming) -> begin
((
# 401 "FStar.Syntax.Subst.fst"
let _35_597 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_597.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_597.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 404 "FStar.Syntax.Subst.fst"
let x' = (
# 404 "FStar.Syntax.Subst.fst"
let _35_601 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_266 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_601.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_601.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_266}))
in (
# 405 "FStar.Syntax.Subst.fst"
let sub = (let _124_267 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_267)
in ((
# 406 "FStar.Syntax.Subst.fst"
let _35_605 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_605.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_605.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 409 "FStar.Syntax.Subst.fst"
let x' = (
# 409 "FStar.Syntax.Subst.fst"
let _35_609 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_268 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_609.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_609.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_268}))
in (
# 410 "FStar.Syntax.Subst.fst"
let sub = (let _124_269 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_269)
in ((
# 411 "FStar.Syntax.Subst.fst"
let _35_613 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_613.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_613.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 414 "FStar.Syntax.Subst.fst"
let x = (
# 414 "FStar.Syntax.Subst.fst"
let _35_619 = x
in (let _124_270 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_619.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_619.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_270}))
in (
# 415 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 416 "FStar.Syntax.Subst.fst"
let _35_623 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_623.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_623.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (
# 418 "FStar.Syntax.Subst.fst"
let _35_629 = (aux [] [] p)
in (match (_35_629) with
| (p, sub, _35_628) -> begin
(p, sub)
end)))))

# 421 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_633 -> (match (_35_633) with
| (p, wopt, e) -> begin
(
# 422 "FStar.Syntax.Subst.fst"
let _35_636 = (open_pat p)
in (match (_35_636) with
| (p, opening) -> begin
(
# 423 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_273 = (subst opening w)
in Some (_124_273))
end)
in (
# 426 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 429 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _124_278 = (closing_subst bs)
in (subst _124_278 t)))

# 430 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _124_283 = (closing_subst bs)
in (subst_comp _124_283 c)))

# 431 "FStar.Syntax.Subst.fst"
let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (
# 432 "FStar.Syntax.Subst.fst"
let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(
# 435 "FStar.Syntax.Subst.fst"
let x = (
# 435 "FStar.Syntax.Subst.fst"
let _35_656 = x
in (let _124_290 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_656.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_656.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_290}))
in (
# 436 "FStar.Syntax.Subst.fst"
let s' = (let _124_291 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_291)
in (let _124_292 = (aux s' tl)
in ((x, imp))::_124_292)))
end))
in (aux [] bs)))

# 440 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 441 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 442 "FStar.Syntax.Subst.fst"
let _35_663 = lc
in (let _124_299 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_663.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_299; FStar_Syntax_Syntax.cflags = _35_663.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_665 -> (match (()) with
| () -> begin
(let _124_298 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _124_298))
end))}))))

# 445 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 446 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_673) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 452 "FStar.Syntax.Subst.fst"
let _35_681 = (aux sub p)
in (match (_35_681) with
| (p, sub) -> begin
(
# 453 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _124_307 = (aux sub p)
in (Prims.fst _124_307))) ps)
in ((
# 454 "FStar.Syntax.Subst.fst"
let _35_684 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_684.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_684.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 457 "FStar.Syntax.Subst.fst"
let _35_701 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_692 _35_695 -> (match ((_35_692, _35_695)) with
| ((pats, sub), (p, imp)) -> begin
(
# 458 "FStar.Syntax.Subst.fst"
let _35_698 = (aux sub p)
in (match (_35_698) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_701) with
| (pats, sub) -> begin
((
# 460 "FStar.Syntax.Subst.fst"
let _35_702 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_702.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_702.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 463 "FStar.Syntax.Subst.fst"
let x = (
# 463 "FStar.Syntax.Subst.fst"
let _35_706 = x
in (let _124_310 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_706.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_706.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_310}))
in (
# 464 "FStar.Syntax.Subst.fst"
let sub = (let _124_311 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_311)
in ((
# 465 "FStar.Syntax.Subst.fst"
let _35_710 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_710.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_710.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 468 "FStar.Syntax.Subst.fst"
let x = (
# 468 "FStar.Syntax.Subst.fst"
let _35_714 = x
in (let _124_312 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_714.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_714.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_312}))
in (
# 469 "FStar.Syntax.Subst.fst"
let sub = (let _124_313 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_313)
in ((
# 470 "FStar.Syntax.Subst.fst"
let _35_718 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_718.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_718.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 473 "FStar.Syntax.Subst.fst"
let x = (
# 473 "FStar.Syntax.Subst.fst"
let _35_724 = x
in (let _124_314 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_724.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_724.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_314}))
in (
# 474 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 475 "FStar.Syntax.Subst.fst"
let _35_728 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_728.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_728.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 478 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_733 -> (match (_35_733) with
| (p, wopt, e) -> begin
(
# 479 "FStar.Syntax.Subst.fst"
let _35_736 = (close_pat p)
in (match (_35_736) with
| (p, closing) -> begin
(
# 480 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_317 = (subst closing w)
in Some (_124_317))
end)
in (
# 483 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 486 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 487 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 488 "FStar.Syntax.Subst.fst"
let _35_749 = (let _124_322 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 489 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _124_322 FStar_List.unzip))
in (match (_35_749) with
| (s, us') -> begin
(s, us')
end))))

# 493 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 494 "FStar.Syntax.Subst.fst"
let _35_754 = (univ_var_opening us)
in (match (_35_754) with
| (s, us') -> begin
(
# 495 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 498 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 499 "FStar.Syntax.Subst.fst"
let _35_760 = (univ_var_opening us)
in (match (_35_760) with
| (s, us') -> begin
(let _124_331 = (subst_comp s c)
in (us', _124_331))
end)))

# 502 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 503 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 504 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 507 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 508 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 509 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 512 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 529 "FStar.Syntax.Subst.fst"
let _35_786 = (FStar_List.fold_right (fun lb _35_779 -> (match (_35_779) with
| (i, lbs, out) -> begin
(
# 531 "FStar.Syntax.Subst.fst"
let x = (let _124_350 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _124_350))
in ((i + 1), ((
# 532 "FStar.Syntax.Subst.fst"
let _35_781 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_781.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_781.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_781.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_781.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.DB ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_35_786) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(
# 534 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 535 "FStar.Syntax.Subst.fst"
let _35_798 = (FStar_List.fold_right (fun u _35_792 -> (match (_35_792) with
| (i, us, out) -> begin
(
# 537 "FStar.Syntax.Subst.fst"
let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UN ((i, FStar_Syntax_Syntax.U_name (u))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_35_798) with
| (_35_795, us, u_let_rec_opening) -> begin
(
# 540 "FStar.Syntax.Subst.fst"
let _35_799 = lb
in (let _124_354 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_799.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_799.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_799.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_354}))
end)))))
in (
# 542 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_opening t)
in (lbs, t)))
end))
end)

# 545 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 547 "FStar.Syntax.Subst.fst"
let _35_811 = (FStar_List.fold_right (fun lb _35_808 -> (match (_35_808) with
| (i, out) -> begin
(let _124_364 = (let _124_363 = (let _124_362 = (let _124_361 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_124_361, i))
in FStar_Syntax_Syntax.NM (_124_362))
in (_124_363)::out)
in ((i + 1), _124_364))
end)) lbs (0, []))
in (match (_35_811) with
| (n_let_recs, let_rec_closing) -> begin
(
# 549 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 550 "FStar.Syntax.Subst.fst"
let _35_820 = (FStar_List.fold_right (fun u _35_816 -> (match (_35_816) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UD ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_35_820) with
| (_35_818, u_let_rec_closing) -> begin
(
# 551 "FStar.Syntax.Subst.fst"
let _35_821 = lb
in (let _124_368 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_821.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_821.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_821.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_821.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_368}))
end)))))
in (
# 552 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_closing t)
in (lbs, t)))
end))
end)

# 555 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_828 -> (match (_35_828) with
| (us, t) -> begin
(
# 556 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 557 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 558 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _35_835 -> (match (_35_835) with
| (x, _35_834) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 559 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 562 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_841 -> (match (_35_841) with
| (us', t) -> begin
(
# 563 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 564 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us')
in (
# 565 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _124_381 = (subst s t)
in (us', _124_381)))))
end))

# 568 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 569 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_853 -> (match (_35_853) with
| (x, _35_852) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




